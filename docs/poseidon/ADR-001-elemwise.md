# ADR-001: Extensión de MatExpr con elemwise

## Estado
Aceptado

## Contexto

AMO-Lean v1.0 tiene un IR (`MatExpr`) optimizado para operaciones lineales:
- `add`: Suma matricial
- `mul`: Multiplicación matriz-vector
- `kron`: Producto Kronecker

Poseidon requiere la S-box `x^α`, una operación **no-lineal** aplicada elemento por elemento. El IR actual no puede representarla.

## Decisión

Añadir un constructor `elemwise` a `MatExpr`:

```lean
inductive ElemOp where
  | pow : Nat → ElemOp        -- x^n
  | custom : String → ElemOp  -- Extensibilidad futura

inductive MatExpr (α : Type) : Nat → Nat → Type where
  | var     : String → MatExpr α m n
  | add     : MatExpr α m n → MatExpr α m n → MatExpr α m n
  | mul     : MatExpr α m p → MatExpr α p n → MatExpr α m n
  | kron    : MatExpr α m n → MatExpr α p q → MatExpr α (m*p) (n*q)
  | elemwise : ElemOp → MatExpr α m n → MatExpr α m n  -- NUEVO
```

### Semántica

```lean
def eval : MatExpr α m n → Matrix α m n
  | .elemwise (.pow k) e => (eval e).map (λ x => x ^ k)
  | ... -- otros casos
```

## Alternativas Consideradas

### Alternativa A: DSL separado para no-linealidad

```lean
inductive NonLinearExpr where
  | sbox : MatExpr → NonLinearExpr
  | compose : NonLinearExpr → NonLinearExpr → NonLinearExpr
```

**Rechazada** porque:
- Duplica infraestructura (evaluador, CodeGen, E-Graph)
- Dificulta optimización conjunta lineal+no-lineal
- Aumenta complejidad del sistema

### Alternativa B: elemwise binario

```lean
| elemwise2 : (α → α → α) → MatExpr α m n → MatExpr α m n → MatExpr α m n
```

**Pospuesta** porque:
- No necesaria para Poseidon (round constants se suman linealmente)
- Puede añadirse después si se necesita Hadamard product
- Mantiene IR mínimo

## Consecuencias

### Positivas

1. **Preservación de tipos**: La firma `MatExpr α m n → MatExpr α m n` garantiza que las dimensiones se preservan por construcción. Lean no requerirá pruebas adicionales.

2. **Integración natural**: `elemwise` se compone con operaciones existentes:
   ```lean
   -- Una ronda de Poseidon
   MatExpr.mul mds (MatExpr.elemwise (.pow 5) (MatExpr.add state rc))
   ```

3. **CodeGen directo**: El generador de código puede emitir S-box optimizada directamente.

### Negativas

1. **E-Graph más complejo**: Necesita reglas adicionales para `elemwise`.

2. **Evaluador extendido**: Debe manejar el nuevo caso.

## Reglas E-Graph

El nodo `elemwise` actúa como **barrera opaca** para evitar explosión de búsqueda:

```lean
-- PERMITIDAS
elemwise f (elemwise g x) → elemwise (f ∘ g) x  -- Fusión
elemwise op (const c) → const (apply op c)      -- Constant folding
elemwise op (transpose M) → transpose (elemwise op M)  -- Conmutación

-- PROHIBIDA (causaría explosión)
elemwise (pow 5) x → x * x * x * x * x  -- NO expandir
```

## Notas de Implementación

1. **ElemOp debe ser Scalar → Scalar**: Esto garantiza que `elemwise` preserva dimensiones trivialmente.

2. **Composición de ElemOp**: Para la regla de fusión, necesitamos:
   ```lean
   def ElemOp.compose : ElemOp → ElemOp → ElemOp
     | .pow m, .pow n => .pow (m * n)  -- (x^m)^n = x^(m*n)
     | _, _ => .custom "composed"       -- Fallback
   ```

3. **Evaluación lazy**: En el E-Graph, no evaluar `elemwise` hasta que sea necesario para extracción.

---

*Fecha*: Enero 2026
*Autores*: Equipo AMO-Lean
