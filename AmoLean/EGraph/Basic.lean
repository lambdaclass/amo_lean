/-
  AMO-Lean: E-Graph Implementation - Phase 2

  Estructuras de datos para E-graphs optimizadas para Lean 4.
  Diseño basado en egg (Willsey et al.) con adaptaciones para evitar
  problemas de memoria con el GC de Lean.

  Principios de diseño:
  - Estructuras planas (Array, HashMap) en lugar de tipos inductivos recursivos
  - Índices como "punteros" para evitar ciclos en el heap
  - Union-find con path compression para equivalencias eficientes
-/

import Std.Data.HashMap
import Std.Data.HashSet
import AmoLean.Basic

namespace AmoLean.EGraph

open AmoLean (Expr VarId)

/-! ## Parte 1: Tipos Básicos y Cost Model -/

/-- Identificador de una clase de equivalencia (índice en array) -/
abbrev EClassId := Nat

/-- Costo "infinito" para representar costo no calculado -/
def infiniteCost : Nat := 1000000000

/-- Modelo de costo para E-graph (compatible con AmoLean.CostModel) -/
structure EGraphCostModel where
  constCost : Nat := 0
  varCost   : Nat := 0
  addCost   : Nat := 1
  mulCost   : Nat := 10
  deriving Repr, Inhabited

/-- Modelo de costo por defecto -/
def defaultCostModel : EGraphCostModel := {}

/-- Operaciones soportadas en el E-graph.
    Cada operación tiene aridad fija y almacena IDs de hijos (no expresiones recursivas). -/
inductive ENodeOp where
  | const : Int → ENodeOp                    -- Constante literal
  | var : Nat → ENodeOp                      -- Variable (índice)
  | add : EClassId → EClassId → ENodeOp      -- Suma de dos e-classes
  | mul : EClassId → EClassId → ENodeOp      -- Multiplicación de dos e-classes
  deriving Repr, BEq, Hashable, Inhabited

/-- Un E-node es una operación con sus hijos ya canonicalizados.
    A diferencia de Expr, los hijos son IDs, no subexpresiones. -/
structure ENode where
  op : ENodeOp
  deriving Repr, BEq, Hashable, Inhabited

namespace ENode

/-- Crear e-node para constante -/
def mkConst (c : Int) : ENode := ⟨.const c⟩

/-- Crear e-node para variable -/
def mkVar (v : Nat) : ENode := ⟨.var v⟩

/-- Crear e-node para suma -/
def mkAdd (a b : EClassId) : ENode := ⟨.add a b⟩

/-- Crear e-node para multiplicación -/
def mkMul (a b : EClassId) : ENode := ⟨.mul a b⟩

/-- Obtener los hijos de un e-node (IDs de e-classes) -/
def children : ENode → List EClassId
  | ⟨.const _⟩ => []
  | ⟨.var _⟩ => []
  | ⟨.add a b⟩ => [a, b]
  | ⟨.mul a b⟩ => [a, b]

/-- Mapear una función sobre los hijos de un e-node -/
def mapChildren (f : EClassId → EClassId) : ENode → ENode
  | ⟨.const c⟩ => ⟨.const c⟩
  | ⟨.var v⟩ => ⟨.var v⟩
  | ⟨.add a b⟩ => ⟨.add (f a) (f b)⟩
  | ⟨.mul a b⟩ => ⟨.mul (f a) (f b)⟩

/-- Calcular el costo local de un e-node (sin contar hijos).
    El costo total requiere sumar los costos de las e-classes hijas. -/
def localCost (cm : EGraphCostModel := defaultCostModel) : ENode → Nat
  | ⟨.const _⟩ => cm.constCost
  | ⟨.var _⟩ => cm.varCost
  | ⟨.add _ _⟩ => cm.addCost
  | ⟨.mul _ _⟩ => cm.mulCost

end ENode

/-! ## Parte 2: E-Class (Clase de Equivalencia) -/

/-- Una clase de equivalencia contiene:
    - nodes: conjunto de e-nodes equivalentes
    - bestCost: costo mínimo conocido (para extracción), infiniteCost si no calculado
    - bestNode: e-node de costo mínimo (para extracción) -/
structure EClass where
  nodes : Std.HashSet ENode           -- Todos los e-nodes en esta clase
  bestCost : Nat := infiniteCost      -- Costo mínimo (infinito = no calculado)
  bestNode : Option ENode := none     -- E-node de menor costo
  deriving Inhabited

namespace EClass

/-- Crear una e-class con un solo nodo y costo inicial.
    El costo debe incluir el costo del nodo más el de sus hijos. -/
def singleton (node : ENode) (cost : Nat) : EClass :=
  { nodes := Std.HashSet.empty.insert node
  , bestCost := cost
  , bestNode := some node }

/-- Crear una e-class con un solo nodo, costo pendiente de calcular -/
def singletonPending (node : ENode) : EClass :=
  { nodes := Std.HashSet.empty.insert node
  , bestCost := infiniteCost
  , bestNode := some node }

/-- Añadir un nodo a una e-class -/
def addNode (ec : EClass) (node : ENode) : EClass :=
  { ec with nodes := ec.nodes.insert node }

/-- Actualizar el mejor nodo si el nuevo tiene menor costo -/
def updateBest (ec : EClass) (node : ENode) (cost : Nat) : EClass :=
  if cost < ec.bestCost then
    { ec with bestCost := cost, bestNode := some node }
  else
    ec

/-- Unir dos e-classes (para merge) -/
def union (ec1 ec2 : EClass) : EClass :=
  let merged := ec1.nodes.fold (init := ec2.nodes) fun acc n => acc.insert n
  { nodes := merged
  , bestCost := min ec1.bestCost ec2.bestCost
  , bestNode := if ec1.bestCost ≤ ec2.bestCost then ec1.bestNode else ec2.bestNode }

/-- Número de nodos en la e-class -/
def size (ec : EClass) : Nat := ec.nodes.size

/-- ¿Tiene costo calculado? -/
def hasCost (ec : EClass) : Bool := ec.bestCost < infiniteCost

end EClass

/-! ## Parte 3: Union-Find (Estructura de Unión Eficiente) -/

/-- Union-Find con path compression.
    Almacena el padre de cada ID. Si parent[i] = i, entonces i es raíz. -/
structure UnionFind where
  parent : Array EClassId
  deriving Inhabited

namespace UnionFind

/-- Crear union-find vacío -/
def empty : UnionFind := ⟨#[]⟩

/-- Crear union-find con n elementos (cada uno es su propia raíz) -/
def init (n : Nat) : UnionFind :=
  ⟨Array.range n⟩

/-- Añadir un nuevo elemento (se convierte en su propia raíz) -/
def add (uf : UnionFind) : (EClassId × UnionFind) :=
  let newId := uf.parent.size
  (newId, ⟨uf.parent.push newId⟩)

/-- Encontrar la raíz canónica de un ID (con path compression).
    Retorna (raíz, union-find actualizado).
    Nota: Usa acceso con runtime check (!) para simplicidad del prototipo. -/
partial def find (uf : UnionFind) (id : EClassId) : (EClassId × UnionFind) :=
  if id < uf.parent.size then
    let parentId := uf.parent[id]!
    if parentId == id then
      (id, uf)
    else
      let (root, uf') := find uf parentId
      -- Path compression: actualizar parent[id] directamente a root
      if id < uf'.parent.size then
        let uf'' := ⟨uf'.parent.set! id root⟩
        (root, uf'')
      else
        (root, uf')
  else
    (id, uf)  -- ID fuera de rango, retornar sin cambios

/-- Unir dos clases. El segundo se convierte en hijo del primero. -/
def union (uf : UnionFind) (id1 id2 : EClassId) : UnionFind :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  if root1 == root2 then
    uf2
  else if root2 < uf2.parent.size then
    ⟨uf2.parent.set! root2 root1⟩
  else
    uf2

/-- Verificar si dos IDs están en la misma clase -/
def equiv (uf : UnionFind) (id1 id2 : EClassId) : (Bool × UnionFind) :=
  let (root1, uf1) := uf.find id1
  let (root2, uf2) := uf1.find id2
  (root1 == root2, uf2)

/-- Número de elementos en el union-find -/
def size (uf : UnionFind) : Nat := uf.parent.size

end UnionFind

/-! ## Parte 4: E-Graph Principal -/

/-- El E-graph principal.

    Componentes:
    - unionFind: estructura de unión para equivalencias
    - hashcons: mapa de e-node → e-class ID (evita duplicados)
    - classes: mapa de e-class ID → datos de la clase
    - worklist: IDs pendientes de procesamiento (para rebuild)
    - dirty: IDs que han sido modificados desde último rebuild -/
structure EGraph where
  unionFind : UnionFind
  hashcons : Std.HashMap ENode EClassId
  classes : Std.HashMap EClassId EClass
  worklist : List EClassId          -- Para rebuild incremental
  dirty : Std.HashSet EClassId      -- Clases modificadas
  deriving Inhabited

namespace EGraph

/-- Crear E-graph vacío -/
def empty : EGraph :=
  { unionFind := UnionFind.empty
  , hashcons := Std.HashMap.empty
  , classes := Std.HashMap.empty
  , worklist := []
  , dirty := Std.HashSet.empty }

/-- Número de e-classes en el grafo -/
def numClasses (g : EGraph) : Nat := g.classes.size

/-- Número de e-nodes en el grafo -/
def numNodes (g : EGraph) : Nat := g.hashcons.size

/-- Encontrar el ID canónico de una e-class -/
def find (g : EGraph) (id : EClassId) : (EClassId × EGraph) :=
  let (canonical, uf') := g.unionFind.find id
  (canonical, { g with unionFind := uf' })

/-- Verificar si dos IDs son equivalentes -/
def equiv (g : EGraph) (id1 id2 : EClassId) : (Bool × EGraph) :=
  let (eq, uf') := g.unionFind.equiv id1 id2
  (eq, { g with unionFind := uf' })

/-- Canonicalizar un e-node (reemplazar hijos con sus raíces canónicas) -/
def canonicalize (g : EGraph) (node : ENode) : (ENode × EGraph) :=
  match node.op with
  | .const _ | .var _ => (node, g)
  | .add a b =>
    let (a', g1) := g.find a
    let (b', g2) := g1.find b
    (ENode.mkAdd a' b', g2)
  | .mul a b =>
    let (a', g1) := g.find a
    let (b', g2) := g1.find b
    (ENode.mkMul a' b', g2)

/-- Añadir un e-node al grafo. Retorna el ID de su e-class (existente o nueva). -/
def add (g : EGraph) (node : ENode) : (EClassId × EGraph) :=
  -- Primero canonicalizar
  let (canonNode, g1) := g.canonicalize node
  -- Buscar en hashcons
  match g1.hashcons.get? canonNode with
  | some existingId =>
    -- Ya existe, retornar ID existente (canonicalizado)
    let (canonId, g2) := g1.find existingId
    (canonId, g2)
  | none =>
    -- Crear nueva e-class (costo pendiente de calcular)
    let (newId, uf') := g1.unionFind.add
    let newClass := EClass.singletonPending canonNode
    let g2 := { g1 with
      unionFind := uf'
      hashcons := g1.hashcons.insert canonNode newId
      classes := g1.classes.insert newId newClass }
    (newId, g2)

/-- Unir dos e-classes. Marca la clase resultante como dirty. -/
def merge (g : EGraph) (id1 id2 : EClassId) : EGraph :=
  let (root1, g1) := g.find id1
  let (root2, g2) := g1.find id2
  if root1 == root2 then g2
  else
    -- Unir en union-find
    let uf' := g2.unionFind.union root1 root2
    -- Combinar datos de las clases
    let class1 := g2.classes.get? root1 |>.getD (EClass.singletonPending (ENode.mkConst 0))
    let class2 := g2.classes.get? root2 |>.getD (EClass.singletonPending (ENode.mkConst 0))
    let mergedClass := class1.union class2
    -- Actualizar estructuras
    { g2 with
      unionFind := uf'
      classes := g2.classes.insert root1 mergedClass
      worklist := root2 :: g2.worklist
      dirty := g2.dirty.insert root1 }

/-- Obtener la e-class de un ID (canonicalizado) -/
def getClass (g : EGraph) (id : EClassId) : (Option EClass × EGraph) :=
  let (canonId, g1) := g.find id
  (g1.classes.get? canonId, g1)

/-! ## Parte 5: Rebuild (Mantenimiento de Invariantes) -/

/-- Procesar un solo e-class ID: re-canonicalizar sus nodos y actualizar hashcons.
    Retorna el grafo actualizado y una lista de pares (oldId, newId) para merges pendientes. -/
private def processClass (g : EGraph) (classId : EClassId) : (EGraph × List (EClassId × EClassId)) :=
  let (canonId, g1) := g.find classId
  match g1.classes.get? canonId with
  | none => (g1, [])
  | some eclass =>
    -- Para cada nodo en la clase, re-canonicalizar y actualizar hashcons
    eclass.nodes.fold (init := (g1, [])) fun (acc, merges) node =>
      let (canonNode, acc1) := acc.canonicalize node
      if canonNode == node then
        -- Nodo ya está canonicalizado, no hay cambios
        (acc1, merges)
      else
        -- Nodo cambió, actualizar hashcons
        -- Primero eliminar la entrada vieja
        let hashcons1 := acc1.hashcons.erase node
        -- Verificar si el nodo canonicalizado ya existe
        match hashcons1.get? canonNode with
        | some existingId =>
          -- El nodo canonicalizado ya existe en otra clase
          -- Necesitamos hacer merge (lo agregamos a la lista)
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc1 with hashcons := hashcons2 }, (canonId, existingId) :: merges)
        | none =>
          -- El nodo canonicalizado es nuevo, actualizar hashcons
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc1 with hashcons := hashcons2 }, merges)

/-- Rebuild: restaurar invariantes del hashcons después de merges.
    Debe llamarse después de una serie de merges antes de hacer queries.

    Algoritmo (basado en egg):
    1. Para cada clase en worklist, re-canonicalizar sus nodos
    2. Si un nodo canonicalizado ya existe en otra clase, hacer merge
    3. Repetir hasta que no haya más trabajo -/
partial def rebuild (g : EGraph) : EGraph :=
  if g.worklist.isEmpty && g.dirty.isEmpty then g
  else
    -- Obtener clases a procesar (dirty + worklist)
    let toProcess := g.worklist ++ g.dirty.toList
    -- Limpiar worklist y dirty
    let g1 := { g with worklist := [], dirty := Std.HashSet.empty }
    -- Procesar cada clase y acumular merges pendientes
    let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
      let (acc', newMerges) := processClass acc classId
      (acc', newMerges ++ merges)
    ) (g1, [])
    -- Aplicar merges pendientes
    let g3 := pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2
    -- Si hubo merges, puede haber más trabajo - recursión
    if g3.worklist.isEmpty && g3.dirty.isEmpty then g3
    else rebuild g3

/-! ## Parte 6: Estadísticas y Debug -/

/-- Estadísticas del E-graph -/
structure Stats where
  numClasses : Nat
  numNodes : Nat
  unionFindSize : Nat
  worklistSize : Nat
  deriving Repr

/-- Obtener estadísticas del grafo -/
def stats (g : EGraph) : Stats :=
  { numClasses := g.numClasses
  , numNodes := g.numNodes
  , unionFindSize := g.unionFind.size
  , worklistSize := g.worklist.length }

/-! ## Parte 7: Conversión desde Expr -/

/-- Añadir una expresión al E-graph recursivamente.
    Retorna el ID de la e-class raíz y el grafo actualizado. -/
def addExpr (g : EGraph) : Expr Int → (EClassId × EGraph)
  | .const c =>
    g.add (ENode.mkConst c)
  | .var v =>
    g.add (ENode.mkVar v)
  | .add e1 e2 =>
    let (id1, g1) := addExpr g e1
    let (id2, g2) := addExpr g1 e2
    g2.add (ENode.mkAdd id1 id2)
  | .mul e1 e2 =>
    let (id1, g1) := addExpr g e1
    let (id2, g2) := addExpr g1 e2
    g2.add (ENode.mkMul id1 id2)

/-- Crear un E-graph desde una expresión -/
def fromExpr (e : Expr Int) : (EClassId × EGraph) :=
  addExpr EGraph.empty e

/-! ## Parte 8: Cálculo de Costos -/

/-- Calcular el costo de un e-node dado los costos de sus hijos.
    Usa el CostModel del E-graph. -/
def nodeCost (cm : EGraphCostModel) (childCosts : EClassId → Nat) : ENode → Nat
  | ⟨.const _⟩ => cm.constCost
  | ⟨.var _⟩ => cm.varCost
  | ⟨.add a b⟩ => cm.addCost + childCosts a + childCosts b
  | ⟨.mul a b⟩ => cm.mulCost + childCosts a + childCosts b

/-- Calcular costos de todas las e-classes (análisis bottom-up).
    Itera hasta convergencia porque las clases pueden tener dependencias circulares. -/
partial def computeCosts (g : EGraph) (cm : EGraphCostModel := defaultCostModel) : EGraph :=
  -- Función auxiliar: obtener el mejor costo de una clase
  let getCost (classes : Std.HashMap EClassId EClass) (id : EClassId) : Nat :=
    let (canonId, _) := g.unionFind.find id
    match classes.get? canonId with
    | some ec => ec.bestCost
    | none => infiniteCost
  -- Una iteración: actualizar costos de todas las clases
  let iterate (classes : Std.HashMap EClassId EClass) : (Std.HashMap EClassId EClass × Bool) :=
    classes.fold (init := (classes, false)) fun (acc, changed) classId eclass =>
      -- Para cada nodo en la clase, calcular su costo
      let (bestCost, bestNode, nodeChanged) := eclass.nodes.fold
        (init := (eclass.bestCost, eclass.bestNode, false))
        fun (curBest, curNode, curChanged) node =>
          let cost := nodeCost cm (getCost acc) node
          if cost < curBest then (cost, some node, true)
          else (curBest, curNode, curChanged)
      if nodeChanged then
        let updatedClass := { eclass with bestCost := bestCost, bestNode := bestNode }
        (acc.insert classId updatedClass, true)
      else
        (acc, changed)
  -- Iterar hasta convergencia (máximo 100 iteraciones para evitar loops infinitos)
  let rec loop (classes : Std.HashMap EClassId EClass) (fuel : Nat) : Std.HashMap EClassId EClass :=
    if fuel == 0 then classes
    else
      let (classes', changed) := iterate classes
      if changed then loop classes' (fuel - 1)
      else classes'
  { g with classes := loop g.classes 100 }

/-! ## Parte 9: Extracción -/

/-- Extraer la mejor expresión de una e-class.
    Requiere que los costos hayan sido calculados previamente. -/
partial def extract (g : EGraph) (id : EClassId) : Option (Expr Int) :=
  let (canonId, g') := g.find id
  match g'.classes.get? canonId with
  | none => none
  | some eclass =>
    match eclass.bestNode with
    | none => none
    | some node =>
      match node.op with
      | .const c => some (.const c)
      | .var v => some (.var v)
      | .add a b =>
        match extract g' a, extract g' b with
        | some e1, some e2 => some (.add e1 e2)
        | _, _ => none
      | .mul a b =>
        match extract g' a, extract g' b with
        | some e1, some e2 => some (.mul e1 e2)
        | _, _ => none

end EGraph

/-! ## Parte 10: Tests Básicos -/

section Tests

open EGraph

-- Test 1: Crear E-graph desde expresión simple
#eval do
  let expr : Expr Int := .add (.var 0) (.const 1)  -- x + 1
  let (rootId, g) := fromExpr expr
  IO.println s!"Test 1: x + 1"
  IO.println s!"  Root ID: {rootId}"
  IO.println s!"  Clases: {g.numClasses}"
  IO.println s!"  Nodos: {g.numNodes}"

-- Test 2: Expresión con sharing (x + x)
#eval do
  let expr : Expr Int := .add (.var 0) (.var 0)  -- x + x
  let (rootId, g) := fromExpr expr
  IO.println s!"Test 2: x + x"
  IO.println s!"  Root ID: {rootId}"
  IO.println s!"  Clases: {g.numClasses} (esperado: 2 - una para x, una para x+x)"
  IO.println s!"  Nodos: {g.numNodes}"

-- Test 3: Merge y rebuild
#eval do
  let expr1 : Expr Int := .mul (.var 0) (.const 1)  -- x * 1
  let expr2 : Expr Int := .var 0                     -- x
  let (id1, g1) := fromExpr expr1
  let (id2, g2) := g1.addExpr expr2
  IO.println s!"Test 3: Merge x*1 con x"
  IO.println s!"  Antes del merge: {g2.numClasses} clases"
  let g3 := g2.merge id1 id2  -- x * 1 = x
  let g4 := g3.rebuild
  IO.println s!"  Después del merge+rebuild: {g4.numClasses} clases"

-- Test 4: Cálculo de costos y extracción
#eval do
  let expr : Expr Int := .add (.mul (.var 0) (.const 1)) (.const 0)  -- x*1 + 0
  let (rootId, g1) := fromExpr expr
  let g2 := g1.computeCosts
  IO.println s!"Test 4: Cálculo de costos para x*1 + 0"
  IO.println s!"  Clases: {g2.numClasses}"
  match g2.extract rootId with
  | some extracted => IO.println s!"  Extraído: {repr extracted}"
  | none => IO.println "  Error: no se pudo extraer"

-- Test 5: Stats
#eval do
  let expr : Expr Int := .mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))  -- (x+y)*(x+y)
  let (_, g) := fromExpr expr
  let stats := g.stats
  IO.println s!"Test 5: Stats para (x+y)*(x+y)"
  IO.println s!"  {repr stats}"

end Tests

end AmoLean.EGraph
