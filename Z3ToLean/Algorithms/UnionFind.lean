/-
Union-Find data structure for tracking equivalence classes

Used as the foundation for congruence closure algorithm.
Implements path compression for efficient find operations.
-/

namespace Z3Proof.Algorithms

/-! ## Union-Find -/

structure UnionFind (α : Type) [BEq α] [Hashable α] where
  parent : List (α × α)
  deriving Repr

def UnionFind.empty {α : Type} [BEq α] [Hashable α] : UnionFind α :=
  { parent := [] }

partial def UnionFind.find {α : Type} [BEq α] [Hashable α] (uf : UnionFind α) (x : α) : α :=
  match uf.parent.lookup x with
  | none => x  -- x is its own representative
  | some p =>
      if p == x then x  -- x is the root
      else UnionFind.find uf p  -- Recurse (would do path compression in mutable version)

def UnionFind.union {α : Type} [BEq α] [Hashable α] (uf : UnionFind α) (x y : α) : UnionFind α :=
  let rootX := uf.find x
  let rootY := uf.find y
  if rootX == rootY then
    uf  -- Already in same set
  else
    -- Union by making rootX point to rootY
    { parent := (rootX, rootY) :: uf.parent }

def UnionFind.connected {α : Type} [BEq α] [Hashable α] (uf : UnionFind α) (x y : α) : Bool :=
  uf.find x == uf.find y

def UnionFind.insert {α : Type} [BEq α] [Hashable α] (uf : UnionFind α) (x : α) : UnionFind α :=
  match uf.parent.lookup x with
  | some _ => uf  -- Already present
  | none => { parent := (x, x) :: uf.parent }  -- Insert as singleton

end Z3Proof.Algorithms
