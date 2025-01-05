import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.Util.Superscript

namespace SSet.Truncated

scoped macro:1000 (priority := high)
  X:term " _[" n:term "]"t:subscript(term) : term =>
    `(($X : SSet.Truncated $(⟨t.raw[0]⟩)).obj
      (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

scoped macro:1000 (priority := high)
  X:term " _[" n:term "," p:term "]"t:subscript(term) : term =>
    `(($X : SSet.Truncated $(⟨t.raw[0]⟩)).obj
      (Opposite.op ⟨SimplexCategory.mk $n, $p⟩))

end SSet.Truncated

namespace SimplexCategory.Truncated
open CategoryTheory SimplexCategory

/-- The truncated form of the inclusion functor. -/
def incl {n m : ℕ} (h : n ≤ m) : Truncated n ⥤ Truncated m where
  obj a := ⟨a.1, a.2.trans h⟩
  map := id

lemma incl_comp_inclusion {n m : ℕ} (h : n ≤ m) :
    incl h ⋙ inclusion m = inclusion n := rfl

end SimplexCategory.Truncated

universe v u

namespace SimplicialObject.Truncated
open CategoryTheory SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- The truncated form of the truncation functor. -/
def trunc {n m : ℕ} (h : n ≤ m) : Truncated C m ⥤ Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl h).op

lemma truncation_comp_trunc {n m : ℕ} (h : n ≤ m) :
    truncation m ⋙ trunc C h = truncation n := rfl

end SimplicialObject.Truncated

namespace SSet.Truncated
open CategoryTheory SimplexCategory Simplicial

/-- The truncated form of the truncation functor. -/
def trunc {n m : ℕ} (h : n ≤ m) : Truncated m ⥤ Truncated n :=
  SimplicialObject.Truncated.trunc (Type u) h

lemma truncation_comp_trunc {n m : ℕ} (h : n ≤ m) :
    truncation m ⋙ trunc h = truncation n := rfl

/-- A path of length `n` in a 1-truncated simplicial set is a directed path of
`n` edges. -/
@[ext]
structure Path₁ (X : Truncated.{u} 1) (n : ℕ) where
  vertex (i : Fin (n + 1)) : X _[0]₁
  arrow (i : Fin n) : X _[1]₁
  arrow_src (i : Fin n) : X.map (δ 1).op (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin n) : X.map (δ 0).op (arrow i) = vertex i.succ

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

/-- A path in any `n + 1`-truncated simplicial set `X` is defined by further
1-truncating `X`, then taking the 1-truncated path. -/
abbrev Path : ℕ → Type u := trunc (by omega) |>.obj X |>.Path₁

/-- The spine of an `n + 1`-simplex in an `n + 1`-truncated simplicial set `X`
is the path of edges of length `n + 1` formed by traversing through its
vertices in order. -/
def spine (Δ : X _[n + 1, by rfl]ₙ₊₁) : Path X (n + 1) where
  vertex i := X.map (SimplexCategory.const [0] [n + 1] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    erw [← FunctorToTypes.map_comp_apply, ← op_comp (f := (δ 1).op.unop)]
    simp
  arrow_tgt i := by
    erw [← FunctorToTypes.map_comp_apply, ← op_comp (f := (δ 0).op.unop)]
    simp

/-- An `n + 1`-truncated simplicial set satisfies the strict Segal condition
if its `n + 1`-simplices are uniquely determined by their spine. -/
class StrictSegal where
  spineToSimplex : Path X (n + 1) → X _[n + 1, by rfl]ₙ₊₁
  spine_spineToSimplex : X.spine ∘ spineToSimplex = id
  spineToSimplex_spine : spineToSimplex ∘ X.spine = id

end SSet.Truncated

namespace SSet
open Truncated CategoryTheory SimplexCategory Simplicial

variable (X : SSet.{u})

/-- A path in a simplicial set is defined by 1-truncating, then taking the
1-truncated path. -/
abbrev Path : ℕ → Type u := truncation 1 |>.obj X |>.Path₁

/-- The spine of an `n + 1` simplex in `X` is the path of edges of length
`n + 1` formed by traversing in order through the vertices of the `n + 1`
truncation. -/
abbrev spine {n : ℕ} : X _[n + 1] → X.Path (n + 1) :=
  truncation (n + 1) |>.obj X |>.spine

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices
are uniquely determined by their spine. -/
-- TODO: can we define this directly in terms of `Truncated.StrictSegal`?
class StrictSegal where
  spineToSimplex {n : ℕ} : Path X (n + 1) → X _[n + 1]
  spine_spineToSimplex {n : ℕ} : X.spine (n := n) ∘ spineToSimplex = id
  spineToSimplex_spine {n : ℕ} : spineToSimplex ∘ X.spine (n := n) = id

instance strictSegal_of_strictSegal
    [∀ n : ℕ, Truncated.StrictSegal ((truncation (n + 1)).obj X)] :
    StrictSegal X where
  spineToSimplex {n} :=
    Truncated.StrictSegal.spineToSimplex (X := (truncation (n + 1)).obj X)
  spine_spineToSimplex := Truncated.StrictSegal.spine_spineToSimplex
  spineToSimplex_spine := Truncated.StrictSegal.spineToSimplex_spine

end SSet
