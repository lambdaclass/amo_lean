# AMO-Lean: Optimización Formal de Programas mediante Equality Saturation en Tipos Dependientes

*Por [Tu Nombre/Organización]*

Los compiladores verificados tradicionales, como CompCert, se centran en la preservación semántica de código C ya escrito, limitando su capacidad para realizar optimizaciones algorítmicas radicales. Por otro lado, generadores de código de dominio específico como SPIRAL producen código extremadamente eficiente pero carecen de garantías formales de corrección integradas en el asistente de pruebas.

AMO-Lean es un motor de optimización implementado nativamente en Lean 4 que combina ambas tradiciones. El sistema compila teoremas algebraicos de Mathlib en reglas de reescritura que alimentan un motor de equality saturation puramente funcional, y emite código C con intrinsics SIMD acompañado de anotaciones de trazabilidad formal (*Proof Anchors*).

El resultado es un optimizador donde cada transformación aplicada tiene una prueba Lean correspondiente, y donde el código emitido puede ser auditado contra la lógica formalmente verificada.

A continuación, diseccionamos los cuatro pilares arquitectónicos del sistema.


## 1. El DSL Algebraico: SPIRAL Elevado a Teoría de Tipos

### Qué es un DSL y por qué necesitamos uno

Un DSL (*Domain-Specific Language*) es un lenguaje de programación diseñado para un dominio concreto, en contraste con un lenguaje de propósito general como Rust o C. Un DSL no necesita manejar threads, I/O o gestión de memoria — solo necesita expresar con precisión las operaciones de su dominio. A cambio de esa restricción, gana una propiedad: el compilador puede razonar exhaustivamente sobre los programas escritos en él, porque el espacio de programas posibles es acotado y estructurado.

En AMO-Lean, el DSL es un tipo inductivo de Lean 4 llamado `MatExpr`. Es la representación intermedia sobre la que opera todo el sistema: las reglas de reescritura se aplican sobre él, el E-Graph lo almacena, y el codegen lo traduce a C. Un programa en este DSL no describe *cómo* computar una transformada — describe *qué* transformada es, como una fórmula algebraica. El optimizador se encarga de derivar el *cómo*.

### SPIRAL: Optimización como Álgebra de Matrices

Para entender el DSL, hay que entender SPIRAL.

SPIRAL es un proyecto de Carnegie Mellon (Franchetti, Püschel et al.) que ataca un problema concreto: generar código altamente optimizado para transformadas lineales (FFT, NTT, DCT, WHT) sin escribir implementaciones a mano. La idea central es que todas estas transformadas pueden representarse como productos de matrices dispersas estructuradas, y que las optimizaciones — reordenar operaciones, vectorizar, mejorar localidad de cache — son equivalentes a aplicar identidades algebraicas sobre esas matrices.

El insight de SPIRAL es que una FFT de tamaño $N$ no es un algoritmo: es una factorización. La identidad de Cooley-Tukey lo explicita:

$$DFT_{mn} = (DFT_m \otimes I_n) \cdot D_n^{mn} \cdot (I_m \otimes DFT_n) \cdot L_n^{mn}$$

Esto dice: para computar una DFT de tamaño $m \times n$, aplicar una permutación de stride ($L$), luego $n$ DFTs pequeñas de tamaño $m$ en paralelo ($I_m \otimes DFT_n$), luego multiplicar por factores twiddle ($D$), luego $m$ DFTs de tamaño $n$ en paralelo ($DFT_m \otimes I_n$). Cada factor es una matriz dispersa con estructura explotable.

El operador central es el **Producto de Kronecker** $A \otimes B$. Si $A$ es $m \times m$ y $B$ es $n \times n$, entonces $A \otimes B$ es una matriz $(mn) \times (mn)$ que aplica $A$ a "bloques" y $B$ dentro de cada bloque. En términos de código, $I_m \otimes A_n$ es un `for` loop de $m$ iteraciones aplicando $A$ a segmentos contiguos de tamaño $n$. Y $A_m \otimes I_n$ es la misma operación pero con datos intercalados (*strided*). SPIRAL transforma entre estas dos formas usando permutaciones de stride, y elige la que mejor se mapea al hardware.

Lo que AMO-Lean adopta de SPIRAL:

1. **Representación**: las transformadas son fórmulas de matrices, no código imperativo.
2. **Optimización por reescritura algebraica**: optimizar es aplicar identidades (Cooley-Tukey, factorización de stride, distribución de Kronecker).
3. **Pipeline de lowering**: la fórmula algebraica se baja (*lower*) a una representación intermedia Σ-SPL con loops explícitos, y de ahí a C con SIMD.

Lo que AMO-Lean añade: en SPIRAL, las identidades algebraicas son axiomas *hardcodeados* en el compilador (escrito en GAP/OCaml). Si una identidad tiene un error, el compilador genera código incorrecto silenciosamente. En AMO-Lean, cada identidad es un teorema verificado por el kernel de Lean 4.

### Tipos y Constructores: La Estructura del DSL

Para lectores familiarizados con `enum` en Rust, un tipo inductivo de Lean es conceptualmente similar: define un tipo cerrado con un conjunto finito de *variantes* (llamadas **constructores**). La diferencia es que en Lean los constructores pueden estar **indexados por valores** — las dimensiones de la matriz son parte del tipo, no datos en runtime.

El DSL de AMO-Lean define `MatExpr α m n`: una expresión matricial sobre un tipo de coeficientes `α`, con `m` filas y `n` columnas. Los constructores principales son:

```lean
inductive MatExpr (α : Type) : Nat → Nat → Type where
  | identity (n : Nat) : MatExpr α n n             -- I_n
  | dft (n : Nat) : MatExpr α n n                  -- DFT simbólica
  | ntt (n p : Nat) : MatExpr α n n                -- NTT en Z_p
  | twiddle (n k : Nat) : MatExpr α n n            -- Factores twiddle
  | perm : Perm n → MatExpr α n n                  -- Permutación
  | kron : MatExpr α m₁ n₁ → MatExpr α m₂ n₂      -- A ⊗ B
         → MatExpr α (m₁ * m₂) (n₁ * n₂)
  | compose : MatExpr α m k → MatExpr α k n        -- A · B
            → MatExpr α m n
  | add : MatExpr α m n → MatExpr α m n            -- A + B
        → MatExpr α m n
  -- ... y otros
```

Dos puntos a notar:

1. **Las dimensiones son parte del tipo.** `compose` solo acepta matrices donde la dimensión interna $k$ coincide — $A_{m \times k} \cdot B_{k \times n}$. Lean rechaza en tiempo de compilación una composición con dimensiones incompatibles. Esto es imposible de expresar en un `enum` de Rust sin recurrir a `PhantomData` y traits bounds complejos.

2. **Los constructores simbólicos no expanden.** `dft 1024` no almacena una matriz de $1024 \times 1024$ entradas — es un solo nodo que *representa* esa transformada. La factorización de Cooley-Tukey aplicada a `dft 1024` produce un árbol de ~$\log_2(1024) = 10$ niveles con `kron`, `compose`, `twiddle` y `perm`. Esto mantiene la representación en $O(\log N)$ nodos para una transformada de tamaño $N$, que es lo que permite al E-Graph operar eficientemente sobre transformadas grandes.

### Permutaciones Simbólicas

El operador $L_n^{mn}$ (stride permutation) modela reordenamientos de memoria. Concretamente, mapea el índice $i$ a $(i \bmod m) \cdot n + \lfloor i / m \rfloor$, que es la transposición de una matriz $m \times n$ almacenada en row-major.

En lugar de emitir código de copia inmediatamente, AMO-Lean mantiene las permutaciones como datos simbólicos (`Perm.lean`), componiéndolas y simplificándolas algebraicamente antes de la generación de código. Las permutaciones también son un tipo inductivo indexado por su tamaño:

```lean
inductive Perm : Nat → Type where
  | identity : Perm n
  | stride : (m n : Nat) → Perm (m * n)
  | bitRev : (k : Nat) → Perm (2^k)
  | compose : Perm n → Perm n → Perm n
  | tensor : Perm m → Perm n → Perm (m * n)
  -- ...
```

El módulo incluye pruebas formales de propiedades algebraicas clave:
- **Inversión de stride**: `stride_inverse_eq` demuestra que $L_n^{mn} \cdot L_m^{mn} = I_{mn}$, probada por aritmética modular sobre los índices.
- **Bit-reversal como involución**: `bitReverse_involution` prueba que aplicar bit-reversal dos veces es la identidad. La prueba procede por inducción sobre el número de bits, con lemas auxiliares que descomponen la relación entre el bit más significativo y el menos significativo del resultado.
- **Distribución del producto tensorial**: `tensor_compose_pointwise` prueba que $(P_1 \otimes Q_1) \cdot (P_2 \otimes Q_2) = (P_1 \cdot P_2) \otimes (Q_1 \cdot Q_2)$, una identidad fundamental para reordenar operaciones SPIRAL.

La diferencia con SPIRAL es que estas identidades no son axiomas implícitos del compilador, sino teoremas verificados en Lean. Con una excepción que es necesario documentar: el producto tensorial de permutaciones requiere un axioma computacionalmente verificable (`applyIndex_tensor_eq`) debido a una limitación del kernel de Lean 4 con el *splitter* para tipos inductivos indexados. El axioma establece que `applyIndex (tensor p q) i` computa lo mismo que una función auxiliar `applyTensorDirect` — ambas definiciones son idénticas algorítmicamente, pero Lean no puede generar la ecuación automáticamente para el pattern matching sobre el tipo indexado `Perm n`. El axioma se valida exhaustivamente por `#eval` para todos los tamaños concretos usados en el sistema.


## 2. El Motor de Equality Saturation

### Qué es un E-Graph

Para entender equality saturation hay que entender primero el problema que resuelve.

Consideremos un optimizador que tiene dos reglas: $a \times 1 \to a$ y $a \times (b + c) \to a \times b + a \times c$. Dada la expresión $x \times (1 + y)$, un rewriter convencional debe elegir qué regla aplicar primero. Si aplica la distribución, obtiene $x \times 1 + x \times y$, y luego puede simplificar a $x + x \times y$. Pero si hubiera otra regla que simplifica $1 + y$ directamente, la decisión de distribuir primero podría haber sido subóptima. El problema es que la reescritura convencional es **destructiva**: aplicar una regla descarta la expresión original. El resultado depende del orden de aplicación, y encontrar el orden óptimo es en general un problema de búsqueda exponencial.

Un **E-Graph** (*Equality Graph*) resuelve esto representando *simultáneamente* todas las formas equivalentes de una expresión. Es una estructura de datos que almacena un conjunto de expresiones agrupadas en **clases de equivalencia**: si dos expresiones se han demostrado iguales, pertenecen a la misma clase.

Concretamente, un E-Graph tiene dos componentes:

1. **E-Nodes**: nodos que representan operaciones. Un e-node para $a + b$ almacena el operador `+` y referencias a las *clases* de $a$ y de $b$ (no a nodos concretos). Esto es clave: como los hijos apuntan a clases, no a expresiones específicas, un solo e-node para `+` implícitamente representa la suma de *cualquier* par de representantes de esas clases.

2. **E-Classes**: conjuntos de e-nodes que se han demostrado equivalentes. Cuando una regla de reescritura establece que $e_1 = e_2$, los e-nodes de $e_1$ y $e_2$ se fusionan (*merge*) en la misma clase.

**Equality saturation** es el proceso de aplicar *todas* las reglas de reescritura exhaustivamente hasta que ninguna produzca nuevas equivalencias (punto fijo) o se exceda un límite. El resultado no es una expresión óptima — es un E-Graph que contiene *todas* las expresiones equivalentes descubiertas. Luego, una fase de **extracción** selecciona la mejor según un modelo de costos.

La ventaja: el orden de aplicación de las reglas es irrelevante. Todas las reglas se aplican en paralelo lógico. No hay backtracking.

### Un E-Graph en un Lenguaje Funcional Puro

La implementación de referencia de E-Graphs es [`egg`](https://egraphs-good.github.io/) (Willsey et al., 2021), escrita en Rust. `egg` usa `Vec<T>` con índices como punteros implícitos, aprovechando la mutabilidad controlada de Rust para operaciones de merge eficientes.

Implementar la misma estructura en Lean 4 — un lenguaje funcional puro — presenta desafíos de diseño distintos. Lean garantiza pureza referencial: no hay mutación observable, no hay punteros, no hay aliasing. Esto es lo que permite al kernel de Lean verificar pruebas, pero también significa que las estructuras de datos cíclicas o densamente enlazadas deben diseñarse con cuidado para no generar presión excesiva sobre el manejo de memoria.

En `EGraph/Basic.lean`, AMO-Lean evita las estructuras recursivas inductivas (árboles, listas enlazadas de nodos) que serían la elección idiomática en Lean. En su lugar, usa una arquitectura de **tablas hash planas con índices enteros** — conceptualmente más cercana a un ECS (*Entity-Component-System*) que a un grafo funcional:

- **Nodos como datos planos**: Un `ENode` almacena una operación y los `EClassId` (alias de `Nat`) de sus hijos. No contiene subestructuras recursivas:

  ```lean
  inductive ENodeOp where
    | const : Int → ENodeOp
    | var : Nat → ENodeOp
    | add : EClassId → EClassId → ENodeOp
    | mul : EClassId → EClassId → ENodeOp
    | pow : EClassId → Nat → ENodeOp
  ```

- **Hashconsing**: Un `Std.HashMap ENode EClassId` garantiza la unicidad estructural de los nodos. Si dos subexpresiones son estructuralmente idénticas, comparten el mismo e-node. Esto permite comprobaciones de equivalencia en $O(1)$ por comparación de identificadores enteros.

- **Union-Find con path compression**: La estructura de clases de equivalencia se gestiona mediante un union-find implementado sobre `Array EClassId`, con compresión de caminos durante `find`. Lean 4 implementa internamente un mecanismo de *reference counting*: cuando un `Array` tiene un solo propietario (refcount = 1), operaciones como `set!` mutan in-place sin copiar. Esto da rendimiento comparable al caso mutable para el patrón de uso del union-find, donde el array se modifica secuencialmente dentro de una función.

Esta arquitectura evita ciclos en el heap y mantiene la pureza referencial requerida por el kernel de Lean. El E-Graph matricial (`EGraph/Vector.lean`) extiende este mismo diseño con nodos `MatENodeOp` que incluyen productos de Kronecker, permutaciones, factores twiddle y operaciones de transposición como variantes de primer nivel.

### Saturación y E-Matching

El motor de saturación (`Saturate.lean`) es una función pura:

```lean
def saturate (g : EGraph) (rules : List RewriteRule)
    (config : SaturationConfig) : SaturationResult
```

No hay estado global, ni mónadas, ni side effects. El E-Graph entra, el E-Graph saturado sale. Cada iteración aplica todas las reglas sobre todas las clases, instancia los lados derechos que matchean, fusiona las clases correspondientes, y ejecuta `rebuild` para restaurar los invariantes del hashcons. El proceso termina cuando se alcanza un punto fijo o se excede un límite configurable de nodos/iteraciones.

El módulo `EMatch.lean` implementa **e-matching**: dado un patrón LHS (por ejemplo, `?a * (?b + ?c)`) y una clase del E-Graph, el matcher busca todas las asignaciones de las variables de patrón (`?a`, `?b`, `?c`) que hacen que el patrón coincida con algún nodo de la clase. Cuando encuentra una, el sistema instancia el RHS con esas asignaciones, añade el resultado al grafo, y fusiona (*merge*) la clase del LHS con la del RHS.

Nótese lo que *no* ocurre: el nodo original no se destruye. El merge solo establece que dos clases son equivalentes. Esto es lo que hace a equality saturation no-destructiva y libre de dependencia en el orden de aplicación de reglas.

**Control de explosión combinatoria.** Hay reglas que amenazan con hacer crecer el E-Graph indefinidamente. La conmutatividad ($a + b \to b + a$) aplicada una vez produce una expresión nueva; aplicada de nuevo, regenera la original; y así en un ciclo infinito. AMO-Lean implementa dos estrategias en `Optimize.lean`:

1. **Reglas dirigidas**: Cada `OptRule` tiene una clasificación (`.reducing`, `.structural`, `.expanding`) y un `costDelta` que estima si la regla reduce o aumenta el costo de la expresión. Solo las reglas *reducing* están en el conjunto seguro por defecto.
2. **Orden canónico**: Para operaciones conmutativas, un hashing estructural determinista (`exprHash`) impone un orden preferente sobre los operandos: si `hash(a) > hash(b)`, solo se almacena `a + b`, nunca `b + a`. Esto elimina la necesidad de la regla bidireccional de conmutatividad. El tradeoff es explícito: se sacrifica completitud teórica (el E-Graph no explorará *todas* las formas comutadas posibles) a cambio de terminación garantizada. En la práctica, para las optimizaciones de dominio de señales que nos interesan, este tradeoff es aceptable.


## 3. El Puente de Confianza: Reglas Verificadas y MetaM

En la mayoría de los compiladores, las optimizaciones ($x \times 0 \to 0$, factorización, distribución) son asunciones implícitas en el código C++ del compilador. Si una regla es incorrecta, el compilador produce silenciosamente código incorrecto. No hay mecanismo dentro del compilador que *demuestre* que la transformación preserva el significado del programa.

En AMO-Lean, cada regla de reescritura tiene un teorema Lean correspondiente que prueba la preservación de la semántica denotacional. Y el mecanismo que conecta esos teoremas con el optimizador — el que convierte pruebas formales en reglas ejecutables — es la mónada de metaprogramación `MetaM`.

### Estructura de una Regla Verificada

Como se define en `VerifiedRules.lean`, una regla consta de:

1. Un patrón sintáctico (LHS → RHS).
2. Un teorema formal de igualdad semántica:
   $$\forall \, \texttt{env}, \; \texttt{eval}(\texttt{env}, \texttt{LHS}) = \texttt{eval}(\texttt{env}, \texttt{RHS})$$

Por ejemplo, la distributividad:

```lean
theorem distrib_left_correct (env : VarId → Int) (a b c : Expr Int) :
    eval env (.mul a (.add b c)) = eval env (.add (.mul a b) (.mul a c)) := by
  simp only [eval]
  ring
```

La estructura de esta prueba es representativa. La función `eval` es la **semántica denotacional** del DSL: traduce una expresión sintáctica (`Expr Int`) a su valor semántico (`Int`) dado un entorno de variables. El `simp only [eval]` despliega la definición recursiva de `eval`, reduciendo ambos lados a expresiones aritméticas puras sobre enteros. La táctica `ring` — provista por Mathlib — cierra el goal automáticamente porque la igualdad resultante es una identidad de anillo.

Las pruebas más simples (identidades con 0 y 1) usan lemas de Mathlib directamente: `Int.add_zero`, `Int.mul_one`, `zero_mul`, `add_zero`. Las propiedades de anillo (distributividad, asociatividad) se cierran con `ring`. Las pruebas de potencias requieren inducción sobre listas (`foldl`). AMO-Lean no reimplementa aritmética: *importa* los lemas existentes de Mathlib y los usa como fundamento de corrección.

De las 20 reglas de reescritura del sistema, 19 están formalmente verificadas sin `sorry`. La regla restante (`zero_pow` para el caso general) tiene un teorema con el caso $n+1$ completamente probado (`zero_pow_succ_correct`).

### MetaM: Qué Es y Qué Habilita

Aquí llegamos al componente que distingue a AMO-Lean de un optimizador convencional que simplemente *tiene* pruebas: la capacidad de **convertir automáticamente teoremas en reglas de reescritura**.

Para entender por qué esto importa, consideremos la alternativa. Sin metaprogramación, cada regla del optimizador se escribe a mano dos veces: una como `Pattern → Pattern` para el E-Graph, y otra como teorema para la prueba de corrección. Si las dos definiciones divergen — si el patrón dice `a * (b + c) → a*b + a*c` pero el teorema prueba otra cosa — el sistema es inconsistente sin que nadie lo note. Este es exactamente el tipo de error sutil que la verificación formal debería prevenir.

`MetaM` es la mónada de metaprogramación de Lean 4. Para lectores de Rust, una mónada es similar a un trait como `Future` o `Iterator` que encapsula un patrón de computación; en este caso, `MetaM` encapsula computaciones que tienen acceso al *estado interno del compilador de Lean*. Concretamente, una función que opera en `MetaM` puede:

- **Consultar el entorno**: Acceder a todas las definiciones, teoremas y axiomas cargados en el contexto actual. Esto incluye todo Mathlib. La función `getConstInfo name` devuelve la declaración completa de cualquier constante por su nombre — su tipo, su cuerpo, sus niveles de universo.

- **Inspeccionar la representación interna de las expresiones**: En Lean, todo — tipos, términos, pruebas — se representa como valores del tipo `Lean.Expr`. Una expresión como `a + b = b + a` es internamente una aplicación de `@Eq` a un tipo, con subexpresiones que son aplicaciones de `@HAdd.hAdd` con argumentos de tipo e instancias de typeclass. `MetaM` permite navegar esta estructura, descomponerla, y reconstruirla.

- **Abrir cuantificadores**: Un teorema como `∀ (a b : α), a + b = b + a` en su representación interna es una cadena de `Lean.Expr.forallE`. La función `forallTelescope` abre todos los cuantificadores simultáneamente, creando variables libres frescas para cada uno y exponiendo el cuerpo de la igualdad. Esto permite inspeccionar el LHS y RHS de la conclusión sin tener que parsear manualmente la cadena de `forallE`.

- **Resolver metavariables**: `instantiateMVars` sustituye las metavariables (incógnitas) pendientes en una expresión por sus asignaciones. Esto es necesario porque el elaborador de Lean puede dejar metavariables sin resolver durante la elaboración incremental.

### Cómo AMO-Lean Usa MetaM

El módulo `Meta/CompileRules.lean` define una monad transformer `ConvertM := StateT ConvertState MetaM` que combina MetaM con un estado propio para tracking de variables. El pipeline completo para convertir un teorema en una regla de reescritura es:

1. **Obtener el tipo del teorema**: `getConstInfo name` recupera la declaración. El tipo de un teorema *es* su enunciado — por ejemplo, el tipo de `distrib_left_correct` es `∀ env a b c, eval env (.mul a (.add b c)) = eval env (.add (.mul a b) (.mul a c))`.

2. **Abrir los cuantificadores**: `forallTelescope type fun args body` abre todos los `∀` y expone `body`, que es una igualdad `Eq lhs rhs`.

3. **Extraer LHS y RHS**: `extractEqualityFromExpr` usa `e.eq?` — un helper de MetaM que reconoce la estructura `@Eq.{u} α lhs rhs` — para obtener ambos lados de la igualdad.

4. **Convertir a Pattern**: `exprToPatternAux` recorre recursivamente la `Lean.Expr` del LHS (y del RHS), reconociendo aplicaciones de funciones conocidas:
   - `@HAdd.hAdd _ _ _ _ e₁ e₂` → `Pattern.add p₁ p₂`
   - `@HMul.hMul _ _ _ _ e₁ e₂` → `Pattern.mul p₁ p₂`
   - `@HPow.hPow _ _ _ _ base (lit n)` → `Pattern.pow p n`
   - `Lean.Expr.fvar id` → `Pattern.patVar n` (donde `n` se asigna secuencialmente por variable)
   - `OfNat.ofNat _ (lit v) _` → `Pattern.const v`

   Nótese que la función reconoce tanto las versiones "heterogéneas" (`HAdd.hAdd` con 6 argumentos) como las "homogéneas" (`Add.add` con 4 argumentos) de cada operador. Esto es necesario porque Lean elabora `a + b` de forma diferente dependiendo del contexto.

5. **Emitir la regla**: El resultado es un `RewriteRule` con nombre, patrón LHS y patrón RHS, listo para ser consumido por el E-Graph.

Todo esto se invoca con el comando `#compile_rules`:

```lean
#compile_rules [distrib_left_correct, mul_one_right_correct, add_zero_left_correct]
```

El comando itera sobre los nombres, ejecuta el pipeline para cada uno, y emite las reglas compiladas con un log de diagnóstico. Si un teorema no tiene la forma esperada (no es una igualdad, o usa operadores no soportados), emite un `logWarning` en lugar de fallar silenciosamente.

### Ventaja para el Proyecto

La ventaja de este enfoque no es solo conveniencia. Es **consistencia estructural**: las reglas que el E-Graph aplica se extraen mecánicamente de los mismos teoremas que prueban su corrección. No hay posibilidad de divergencia entre "lo que el optimizador cree que es correcto" y "lo que está formalmente probado". Si alguien modifica un teorema en Mathlib o en el proyecto, `#compile_rules` extrae la nueva versión automáticamente.

Además, MetaM abre la puerta a una funcionalidad que los optimizadores convencionales no tienen: generar reglas de reescritura a partir de *cualquier* teorema de igualdad en Mathlib, sin intervención manual. En principio, toda identidad algebraica que Mathlib conozca — y Mathlib conoce miles — es una optimización potencial para el E-Graph. El módulo actual soporta los operadores del DSL escalar (suma, multiplicación, potencia); extenderlo a los operadores matriciales del DSL SPIRAL es trabajo en progreso.

### Corrección del Rewriter

El teorema central de corrección (`Correctness.lean`) se estructura en capas:

1. `applyFirst_sound`: si todas las reglas en una lista preservan semántica, aplicar la primera que matchee también la preserva.
2. `rewriteBottomUp_sound`: la reescritura bottom-up preserva semántica (por inducción estructural sobre la expresión).
3. `rewriteToFixpoint_sound`: la iteración hasta punto fijo preserva semántica (por inducción sobre el fuel).
4. `simplify_sound`: la función principal de simplificación preserva semántica, componiendo los lemas anteriores con `algebraicRules_sound`.

Este resultado está formalmente demostrado para el rewriter escalar. Para el motor de E-Graph, la corrección se reduce a la corrección de las reglas individuales: dado que cada regla aplicada durante la saturación tiene una prueba independiente, y la operación de `merge` solo añade equivalencias sin destruir nodos, el resultado extraído preserva la semántica de la entrada. La formalización completa de este argumento composicional para el E-Graph es trabajo en progreso.

### Auditoría en CI

El sistema incluye una función de auditoría (`auditOptRules`) que verifica en tiempo de compilación que cada regla del optimizador tiene un teorema correspondiente. Un `#guard` en `VerifiedRules.lean` falla la compilación si el conteo de reglas verificadas no coincide con el esperado.


## 4. Generación de Código, Modelo de Costos y Proof Anchors

### Del Álgebra al Silicio: el Pipeline de Lowering

La generación de código sigue el pipeline de tres etapas de SPIRAL:

1. **MatExpr → Σ-SPL** (`Sigma/Basic.lean`): Las fórmulas matriciales se bajan (*lower*) a la representación intermedia Sigma-SPL, que modela explícitamente los patrones de acceso a memoria. Un producto de Kronecker $I_n \otimes A_m$ se transforma en un loop: $\Sigma_{i=0}^{n-1} (S_{i,m} \cdot A \cdot G_{i,m})$, donde $G$ es un *gather* (lectura con stride) y $S$ es un *scatter* (escritura con stride).

2. **Σ-SPL → Σ-SPL expandido** (`Sigma/Expand.lean`): Las operaciones compuestas se expanden a operaciones elementales con índices concretos.

3. **Σ-SPL → C** (`Sigma/CodeGen.lean`, `Sigma/SIMD.lean`): El código final se emite como C escalar o con intrinsics SIMD. La vectorización sigue el principio SPIRAL: $A \otimes I_\nu$ (donde $\nu$ es el ancho SIMD) se vectoriza trivialmente — cada operación escalar se convierte en una operación SIMD.

### Modelo de Costos y Extracción

Una vez saturado el E-Graph, el sistema contiene una superposición de implementaciones equivalentes. La expresión original y todas las expresiones descubiertas por las reglas de reescritura coexisten en el grafo. Extraer la "mejor" requiere un criterio: eso es el modelo de costos.

El `MatCostModel` es una estructura parametrizable consciente de SIMD:

```lean
structure MatCostModel where
  simdWidth : Nat := 4         -- 4 para AVX2, 8 para AVX-512
  identityCost : Nat := 0      -- Gratis: no genera código
  dftSymbolicCost : Nat := 0   -- Simbólico: se expandirá después
  nttSymbolicCost : Nat := 0   -- Simbólico
  twiddleCost : Nat := 1       -- Multiplicación diagonal (/ simdWidth)
  permCost : Nat := 2          -- Movimiento de datos
  kronCost : Nat := 0          -- Simbólico
  composeCost : Nat := 1       -- Composición
  addCost : Nat := 1           -- Suma matricial
  smulCost : Nat := 1          -- Multiplicación escalar
  transposeCost : Nat := 2     -- Transposición
  scalarPenalty : Nat := 1000  -- Penalización: fallback escalar
```

Las decisiones de diseño son deliberadas:

1. **Operaciones simbólicas cuestan cero.** Un nodo `dft 1024` no genera código por sí solo — será expandido en etapas posteriores del pipeline. Asignarle costo cero en el E-Graph significa que el extractor nunca preferirá una expansión prematura sobre la representación factorizada. Esto preserva la estructura $O(\log N)$ que necesita SPIRAL.

2. **Costos escalados por ancho SIMD.** El costo de twiddle factors y operaciones element-wise (`elemwise`) se divide por `simdWidth`. Esto refleja que una multiplicación vectorial AVX2 procesa 4 elementos al costo de una instrucción. La consecuencia: al cambiar `simdWidth` de 4 a 8, el extractor automáticamente prefiere factorizaciones con mayor paralelismo interno.

3. **Penalización de fallback escalar.** El `scalarPenalty := 1000` es un anti-patrón explícito: si el E-Graph contiene una variante que requiere expansión escalar (sin vectorización), el extractor la evita a toda costa. Esto dirige la búsqueda sin necesidad de reglas negativas.

El algoritmo de extracción es un análisis bottom-up iterativo (`computeCosts`): para cada e-class, se evalúa el costo de cada nodo como `localCost + Σ childCosts`, y se registra el nodo mínimo. El proceso itera hasta convergencia (punto fijo) o un máximo de 100 iteraciones, necesario porque las dependencias entre clases pueden ser circulares.

Este diseño tiene una propiedad que merece ser explícita: **el modelo de costos es el único componente no verificado que afecta la calidad del resultado.** Las reglas de reescritura están formalmente probadas — cualquier expresión extraída del E-Graph es semánticamente correcta. Pero la *optimalidad* del código generado depende enteramente de que los costos reflejen la realidad del hardware. Un modelo de costos incorrecto produce código correcto pero lento.

### Proof Anchors

AMO-Lean introduce el concepto de *Proof Anchors* (anclajes de prueba) en el código generado.

El código C emitido incluye anotaciones estructuradas que documentan las precondiciones, postcondiciones e invariantes de cada bloque:

```c
// PROOF_ANCHOR: fri_fold_parametric
// Preconditions:
//   - n > 0
//   - even, odd, out are non-null
//   - out does not alias even or odd (required for restrict)
// Postconditions:
//   - forall i in [0, n): out[i] == even[i] + alpha * odd[i]
//   - output array is fully initialized
```

Estas anotaciones crean una cadena de trazabilidad que conecta las transformaciones algebraicas verificadas en Lean con bloques específicos del código emitido. No son assertions ejecutables ni verificación formal end-to-end del binario — son documentación estructurada diseñada para facilitar la auditoría humana y la integración futura con herramientas de verificación estática.

La diferencia con un comentario ad-hoc es que los Proof Anchors se generan *sistemáticamente* por el pipeline de codegen (controlados por el flag `proofAnchors` en `CodeGenConfig`) y siguen un formato parseable, lo que permite a herramientas externas extraerlos y cruzarlos contra los teoremas del proyecto Lean.

Un binario verificado es inútil si no es auditable. Los Proof Anchors son el mecanismo de AMO-Lean para hacer auditable la distancia entre la prueba formal y el código ejecutado.


## 5. Portabilidad y Conexiones con el Estado del Arte

La arquitectura de AMO-Lean — un DSL tipado, un E-Graph con reglas verificadas, un modelo de costos parametrizable y un pipeline de codegen con trazabilidad — no es específica del dominio matricial. Los componentes son separables, y la pregunta natural es: ¿a qué otros dominios se puede aplicar este patrón?

### El Patrón General

El patrón que AMO-Lean instancia es:

1. Definir un DSL como tipo inductivo de Lean (con semántica denotacional).
2. Escribir reglas de reescritura como teoremas de preservación semántica.
3. Compilar esas reglas a un E-Graph vía MetaM.
4. Saturar, extraer con un modelo de costos, y emitir código.

Para aplicar esto a un dominio distinto basta con reemplazar `MatExpr` por otro DSL y escribir las reglas correspondientes. El E-Graph, el union-find, el hashconsing, la saturación y la extracción son genéricos — no asumen nada sobre el dominio excepto que los nodos tienen hijos y un costo.

Los candidatos más directos son dominios donde existen identidades algebraicas conocidas y donde la "mejor" implementación depende del contexto (hardware, tamaño del input, precisión requerida):

- **Circuitos aritméticos sobre campos finitos.** La optimización de R1CS (*Rank-1 Constraint Systems*) para ZK presenta una estructura análoga: un mismo cómputo admite múltiples representaciones como sistema de constraints, y la elección afecta el número de constraints y, por tanto, el costo del proof. Wang et al. (RNA, 2024) observan que "existen diferencias significativas en las formas R1CS generadas a partir de programas con la misma semántica subyacente" — exactamente el escenario donde equality saturation produce valor. Hasta la fecha, no existe trabajo publicado que aplique E-Graphs a optimización de circuitos ZK; esto es un problema abierto.

- **Álgebra lineal densa.** SPORES (Wang et al., VLDB 2020) ya demuestra esto: convierte expresiones de álgebra lineal a álgebra relacional, optimiza con equality saturation, y reconvierte. Las reglas de reescritura son completas (cualquier expresión LA equivalente es alcanzable). El modelo de costos de AMO-Lean podría instanciarse para este dominio reemplazando `MatCostModel` por costos de operaciones BLAS.

- **Precisión numérica.** Herbie (Panchekha et al., PLDI 2015, en desarrollo activo) usa equality saturation vía egglog para explorar expresiones de punto flotante matemáticamente equivalentes y seleccionar la más precisa numéricamente. La función objetivo allí no es rendimiento sino error numérico — un caso donde la "función de costo" es radicalmente distinta de la nuestra, pero la maquinaria de E-Graph es idéntica.

### El Problema de Extracción como Optimización Combinatoria

La extracción — seleccionar la mejor expresión de un E-Graph saturado — es NP-hard en general y difícil de aproximar dentro de un factor constante (Goharshady et al., OOPSLA 2024, Distinguished Paper). Esto tiene consecuencias directas para la portabilidad de AMO-Lean a dominios con E-Graphs más grandes.

El extractor actual de AMO-Lean usa un algoritmo greedy bottom-up (similar al de egg): para cada e-class, elige el nodo de menor costo local + costo de hijos. Este algoritmo es óptimo cuando el E-Graph es un DAG, pero puede producir resultados subóptimos cuando hay subexpresiones compartidas (*common subexpressions*): el mismo nodo puede ser hijo de múltiples e-classes, y la extracción greedy no puede capturar esta interacción.

El estado del arte ofrece varias alternativas, ninguna de las cuales elimina la tensión entre optimalidad y eficiencia:

- **ILP (Integer Linear Programming).** TENSAT (Yang et al., MLSys 2021) aplica equality saturation a grafos de cómputo de deep learning y usa ILP para la extracción. Esto garantiza optimalidad pero escala mal: TENSAT necesita podar ciclos del E-Graph como preprocesamiento para reducir el tiempo de resolución del ILP.

- **Extracción diferenciable.** SmoothE (Cai et al., ASPLOS 2025) hace la extracción diferenciable, permitiendo optimización basada en gradientes. Supera a los extractores heurísticos en datasets adversariales donde el greedy falla por subexpresiones comunes.

- **Treewidth parametrizado.** Goharshady et al. (OOPSLA 2024) demuestran que la extracción es polinomial para E-Graphs con treewidth acotado, y presentan un algoritmo parametrizado implementado en Rust que es óptimo hasta treewidth 10.

Para AMO-Lean en su dominio actual (transformadas de tamaño fijo con estructura recursiva), el extractor greedy es suficiente: los E-Graphs resultantes de las factorizaciones SPIRAL son árboles o DAGs poco profundos con sharing limitado. Pero si el sistema se porta a dominios con mayor sharing (circuitos aritméticos, grafos de cómputo de redes neuronales), la elección del extractor se vuelve una decisión arquitectónica no trivial.

### Modelos de Costos Aprendidos

Una línea de investigación directamente relevante para AMO-Lean es la sustitución del modelo de costos manual por uno aprendido:

- Singh (Cambridge, 2022) modela la equality saturation como un MDP (*Markov Decision Process*) y usa PPO (*Proximal Policy Optimization*) para aprender qué reglas aplicar y cuándo detener la saturación.
- E-morphic (DAC 2025) usa un GNN (*Graph Neural Network*) para estimar el costo de los circuitos durante la extracción, entrenado sobre el benchmark OpenABC-D.
- MCTS + EqSat (PACT 2024) usa Monte Carlo Tree Search para guiar tanto la construcción del E-Graph como la extracción, mejorando el speedup de inference de redes neuronales hasta un 11%.

La implicación para AMO-Lean es concreta: el `MatCostModel` es actualmente una tabla de constantes escritas a mano. Si se reemplaza `localCost : MatENode → Nat` por una función aprendida (por ejemplo, un modelo entrenado sobre benchmarks de ejecución real en hardware destino), el pipeline no cambia — las reglas siguen siendo formalmente verificadas, la extracción sigue siendo correcta, pero la calidad del código generado podría mejorar sin esfuerzo manual de ajuste.

Esto no es especulación: la interfaz del modelo de costos en AMO-Lean ya está parametrizada por una estructura (`MatCostModel`) que se pasa como argumento. Sustituirla por un oráculo aprendido requiere cambiar la instanciación, no la arquitectura.

### Conexión con Demostración Automática de Teoremas

La conexión entre E-Graphs y demostración automática de teoremas se materializa en dos direcciones.

**De E-Graphs a pruebas.** lean-egg (Rossel, en desarrollo; paper aceptado en POPL 2026) es una táctica de Lean 4 que usa egg como backend para razonamiento ecuacional. La táctica envía igualdades al E-Graph, satura con las reglas del contexto, y si encuentra que los dos lados de un goal pertenecen a la misma e-class, genera un *witness* de prueba que el kernel de Lean verifica. Esto mantiene la soundness: egg es un oráculo no confiable, y Lean verifica independientemente cada paso. El trabajo de Singher y Shachar (Easter Egg, FMCAD 2024) extiende E-Graphs con "colores" para razonamiento condicional con múltiples asunciones simultáneas, construyendo un prover ecuacional puramente basado en E-Graphs.

**De LLMs a reglas de reescritura.** Los modelos de lenguaje aplicados a demostración formal (DeepSeek-Prover-V2, ReProver, LeanAgent, AlphaProof) operan seleccionando tácticas y premisas para cerrar goals en Lean. Una dirección concreta para AMO-Lean es usar estos modelos para *descubrir* reglas de reescritura: dado un DSL y un conjunto de axiomas, un LLM podría proponer identidades algebraicas candidatas (por ejemplo, "para campos de Mersenne, $x^{2^{31}} = x \cdot (x-1)^{2^{31}-1}$"), y MetaM podría intentar demostrarlas automáticamente con `ring` o `decide`. Las reglas que se demuestran se añaden al E-Graph; las que no, se descartan. Esto convertiría la generación de reglas de reescritura de un proceso manual a un loop semi-automático de propuesta y verificación.

Hay que ser preciso sobre el alcance de esta conexión: los LLMs actuales no son verificadores — producen conjeturas que pueden ser falsas. La ventaja del contexto de AMO-Lean es que la conjetura falsa no tiene consecuencia: si `ring` no puede cerrar el goal, la regla simplemente no se compila. El cost of failure es un intento fallido, no un bug silencioso.


## Estado Actual y Limitaciones

Es importante ser explícitos sobre lo que está formalmente verificado y lo que no:

| Componente | Estado |
|---|---|
| Reglas de reescritura individuales | 19/20 formalmente verificadas |
| Corrección del rewriter escalar | Formalmente demostrada (`rewriteToFixpoint_sound`) |
| Corrección composicional del E-Graph | Argumento informal válido; formalización en progreso |
| Permutaciones (stride, bit-reversal) | Formalmente verificadas (con 1 axioma documentado para tensor) |
| Pipeline MatExpr → Σ-SPL → C | Correcto por testing (1481+ tests); sin prueba formal de la traducción |
| Proof Anchors | Trazabilidad para auditoría; no verificación mecánica end-to-end |

AMO-Lean no pretende ser un compilador verificado end-to-end al nivel de CompCert. Lo que ofrece es un optimizador donde las transformaciones algebraicas — la parte más propensa a errores sutiles — están formalmente verificadas, con trazabilidad explícita hasta el código emitido.


## Conclusión

AMO-Lean demuestra que es viable implementar un motor de equality saturation dentro de un asistente de pruebas con tipos dependientes, sin sacrificar ni el rigor formal ni la capacidad de generar código eficiente. Las técnicas de SPIRAL para representación simbólica de transformadas, combinadas con la infraestructura de pruebas de Mathlib y la metaprogramación de Lean 4, producen un sistema donde optimizar y verificar son la misma actividad.

La arquitectura es portátil: el patrón de DSL tipado + reglas verificadas + E-Graph + modelo de costos no asume estructura matricial. Los avances recientes en extracción óptima (OOPSLA 2024), modelos de costos aprendidos (ASPLOS 2025), y E-Graphs para demostración automática (POPL 2026) sugieren que las técnicas aquí descritas convergen con líneas de investigación activas en compiladores, verificación formal y aprendizaje automático.

El código fuente está disponible en [enlace al repositorio].


## Referencias

- Willsey et al., *egg: Fast and Extensible Equality Saturation*, POPL 2021
- Franchetti et al., *SPIRAL: Code Generation for DSP Transforms*, Proceedings of the IEEE, 2005
- Zhang et al., *egglog: Better Together: Unifying Datalog and Equality Saturation*, PLDI 2023
- Goharshady et al., *Fast and Optimal Extraction for Sparse Equality Graphs*, OOPSLA 2024
- Cai et al., *SmoothE: Differentiable E-Graph Extraction*, ASPLOS 2025
- Yang et al., *TENSAT: Equality Saturation for Tensor Graph Superoptimization*, MLSys 2021
- Rossel et al., *Towards Pen-and-Paper-Style Equational Reasoning in ITPs by Equality Saturation*, POPL 2026
- Wang et al., *SPORES: Sum-Product Optimization via Relational Equality Saturation*, VLDB 2020
- Panchekha et al., *Herbie: Automatically Improving Floating Point Accuracy*, PLDI 2015
- Singher & Shachar, *Easter Egg: Equality Reasoning Based on E-Graphs with Multiple Assumptions*, FMCAD 2024
- Suciu et al., *Semantic Foundations of Equality Saturation*, ICDT 2025
- Yang et al., *LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*, NeurIPS 2023
- Koehler et al., *Guided Equality Saturation*, POPL 2024
