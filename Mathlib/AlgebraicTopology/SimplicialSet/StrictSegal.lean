/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin, Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if, for all `m : ℕ`,
the map `X.spine m : X _[m] → X.Path m` is an equivalence, with equivalence
inverse `spineToSimplex {m : ℕ} : Path X m → X _[m]`. We define this
construction first for `n + 1`-truncated simplicial sets in
`SSet.Truncated.StrictSegal`. The data of a `StrictSegal` simplicial set is
then defined by an `SSet.Truncated.StrictSegal` structure on the
`n + 1`-truncation of `X` for all `n : ℕ`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set
is isomorphic to the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal
which is proven in `Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal`.
-/

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet
namespace Truncated

open SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

private structure StrictSegalAux {n : ℕ} (X : SSet.Truncated.{u} (n + 1)) where
  spineToSimplex : Path X (n + 1) → X _[n + 1]ₙ₊₁
  spine_spineToSimplex : spine X (n + 1) ∘ spineToSimplex = id
  spineToSimplex_spine : spineToSimplex ∘ spine X (n + 1) = id

inductive StrictSegal : {n : ℕ} → SSet.Truncated.{u} n → Type (u + 1) where
  | nil : (X : SSet.Truncated.{u} 0) → StrictSegal X
  | mk {n X} :
    StrictSegalAux X → StrictSegal ((trunc (n + 1) n).obj X) → StrictSegal X

namespace StrictSegal

variable {n : ℕ} {X : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X)

private def aux : StrictSegalAux X :=
  match sx with
  | mk aux _ => aux

def trunc : StrictSegal ((trunc (n + 1) n).obj X) :=
  match sx with
  | mk _ trunc => trunc

def spineToSimplex : Path X (n + 1) → X _[n + 1]ₙ₊₁ :=
  sx.aux.spineToSimplex

def spine_spineToSimplex : spine X (n + 1) ∘ spineToSimplex sx = id :=
  sx.aux.spine_spineToSimplex

def spineToSimplex_spine : spineToSimplex sx ∘ spine X (n + 1) = id :=
  sx.aux.spineToSimplex_spine

@[simp]
lemma spine_spineToSimplex_apply (f : Path X (n + 1)) :
    X.spine (n + 1) _ (sx.spineToSimplex f) = f :=
  congr_fun sx.spine_spineToSimplex f

@[simp]
lemma spineToSimplex_spine_apply (Δ : X _[n + 1]ₙ₊₁) :
    sx.spineToSimplex (X.spine (n + 1) _ Δ) = Δ :=
  congr_fun sx.spineToSimplex_spine Δ

def spineEquiv : X _[n + 1]ₙ₊₁ ≃ Path X (n + 1) where
  toFun := spine X (n + 1)
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

theorem spineInjective : Function.Injective sx.spineEquiv :=
  Equiv.injective _

def spineToDiagonal : Path X (n + 1) → X _[1]ₙ₊₁ :=
  X.map (tr (diag (n + 1))).op ∘ sx.spineToSimplex

end StrictSegal
end Truncated

variable (X : SSet.{u})

/-- A simplicial set `X` is `SSet.StrictSegal` if the `n`-truncation of `X` is
`SSet.Truncated.StrictSegal` for all `n : ℕ`. -/
abbrev StrictSegal := ∀ n : ℕ, truncation n |>.obj X |>.StrictSegal

namespace StrictSegal

variable {X} (sx : StrictSegal X) {n : ℕ}

/- abbrev spineToSimplex : Path X (n + 1) → X _[n + 1] := sx (n + 1) |>.spineToSimplex -/

/-- The inverse to `spine X n`. -/
abbrev spineToSimplex (f : Path X n) : X _[n] :=
  match n with
  | .zero => f.vertex 0
  | .succ n => sx (n + 1) |>.spineToSimplex f

/-- `spineToSimplex` is a right inverse to `spine X n`. -/
lemma spine_spineToSimplex : X.spine n ∘ sx.spineToSimplex = id :=
  match n with
  | .zero => by
    ext f z
    · simp [Fin.eq_zero, SimplicialObject.truncation, Truncated.inclusion]
    · apply finZeroElim z
  | .succ n => sx (n + 1) |>.spine_spineToSimplex

/-- `spineToSimplex` is a left inverse to `spine X n`. -/
lemma spineToSimplex_spine : sx.spineToSimplex ∘ X.spine n = id :=
  match n with
  | .zero => by
    ext f
    simp [SimplicialObject.truncation, Truncated.inclusion]
  | .succ n => sx (n + 1) |>.spineToSimplex_spine

lemma spine_spineToSimplex_apply (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f :=
  match n with
  | .zero => by
    ext z
    · simp [Fin.eq_zero, SimplicialObject.truncation, Truncated.inclusion]
    · apply finZeroElim z
  | .succ n => sx (n + 1) |>.spine_spineToSimplex_apply f

lemma spineToSimplex_spine_apply (Δ : X _[n]) :
    sx.spineToSimplex (X.spine n Δ) = Δ :=
  match n with
  | .zero => by simp [SimplicialObject.truncation, Truncated.inclusion]
  | .succ n => sx (n + 1) |>.spineToSimplex_spine_apply Δ

abbrev spineEquiv (n : ℕ) : X _[n] ≃ Path X n :=
  match n with
  | .zero => by
    refine { toFun := X.spine 0, invFun := sx.spineToSimplex, left_inv := ?_, right_inv := ?_ }
    · simp [Function.LeftInverse, SimplicialObject.truncation, Truncated.inclusion]
    · intro x
      ext i
      · simp [Fin.eq_zero, SimplicialObject.truncation, Truncated.inclusion]
      · apply finZeroElim i
  | .succ n => sx (n + 1) |>.spineEquiv

/-/1-- The fields of `StrictSegal` define an equivalence between `X _[m]` -/
/-and `Path X m`. -1/ -/
/-abbrev spineEquiv (n : ℕ) : X _[n] ≃ Path X n := sx n |>.spineEquiv n -/

theorem spineInjective : Function.Injective (sx.spineEquiv n) :=
  match n with
  | .zero => Equiv.injective _
  | .succ n => sx (n + 1) |>.spineInjective

lemma spineEquiv_symm_coe_fn (n : ℕ) :
    ⇑(sx.spineEquiv n).symm = sx.spineToSimplex :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

/-/1-- The unique existence of an inverse to `spine X n` forall `n : ℕ` implies -/
/-the mere existence of such an inverse. -1/ -/
/-lemma isStrictSegal (sx : StrictSegal X) : IsStrictSegal X := -/
/-  fun n ↦ sx n |>.isStrictSegal -/

/-lemma spineEquiv_coe_fn (n : ℕ) : ⇑(sx.spineEquiv n) = X.spine n := rfl -/

/- lemma spineEquiv_symm_coe_fn (n : ℕ) : -/
/-     ⇑(sx.spineEquiv n).symm = sx.spineToSimplex := rfl -/

/-@[simp] -/
/-theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) : -/
/-    X.map (const [0] [n] i).op (sx.spineToSimplex f) = f.vertex i := -/
/-  sx n |>.spineToSimplex_vertex n _ i f -/

/-@[simp] -/
/-theorem spineToSimplex_arrow (i : Fin n) (f : Path X n) : -/
/-    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i := -/
/-  sx n |>.spineToSimplex_arrow n _ i f -/

/-/1-- In the presence of the strict Segal condition, a path of length `n` can be -/
/-"composed" by taking the diagonal edge of the resulting `n`-simplex. -1/ -/
/-abbrev spineToDiagonal : Path X n → X _[1] := sx n |>.spineToDiagonal n -/

/-lemma spineToDiagonal_def : -/
/-    sx.spineToDiagonal = X.map (diag n).op ∘ sx.spineToSimplex := rfl -/

/-section interval -/

/-variable (f : Path X n) (j l : ℕ) (hjl : j + l ≤ n) -/

/-@[simp] -/
/-theorem spineToSimplex_interval : -/
/-    X.map (subinterval j l hjl).op (sx.spineToSimplex f) = -/
/-      (sx n).spineToSimplex l (by omega) (f.interval j l hjl) := -/
/-  sx n |>.spineToSimplex_interval n _ f j l hjl -/

/-theorem spineToSimplex_edge : -/
/-    X.map (intervalEdge j l hjl).op (sx.spineToSimplex f) = -/
/-      (sx n).spineToDiagonal l (by omega) (f.interval j l hjl) := -/
/-  sx n |>.spineToSimplex_edge n _ f j l hjl -/

/-end interval -/

/-/1-- For any `σ : X ⟶ Y` between `StrictSegal` simplicial sets, `spineToSimplex` -/
/-commutes with `Path.map`. -1/ -/
/-lemma spineToSimplex_map {X Y : SSet.{u}} (sx : StrictSegal X) -/
/-    (sy : StrictSegal Y) {n : ℕ} (f : Path X (n + 1)) (σ : X ⟶ Y) : -/
/-    sy.spineToSimplex (f.map σ) = σ.app _ (sx.spineToSimplex f) := -/
/-  sx (n + 1) |>.spineToSimplex_map (sy _) n (by omega) f ((truncation _).map σ) -/

/-variable (f : Path X (n + 1)) -/
/-variable {i : Fin (n + 1)} {j : Fin (n + 2)} -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-the common vertices will agree with those of the original path `f`. In particular, -/
/-a vertex `i` with `i < j` can be identified with the same vertex in `f`. -1/ -/
/-lemma spine_δ_vertex_lt (h : i.castSucc < j) : -/
/-    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = -/
/-      f.vertex i.castSucc := -/
/-  sx (n + 1) |>.spine_δ_vertex_lt n (by omega) f h -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original -/
/-path. -1/ -/
/-lemma spine_δ_vertex_ge (h : j ≤ i.castSucc) : -/
/-    (X.spine n (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ := -/
/-  sx (n + 1) |>.spine_δ_vertex_ge n (by omega) f h -/

/-variable {i : Fin n} {j : Fin (n + 2)} -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-the common arrows will agree with those of the original path `f`. In particular, -/
/-an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -1/ -/
/-lemma spine_δ_arrow_lt (h : i.succ.castSucc < j) : -/
/-    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc := -/
/-  sx (n + 1) |>.spine_δ_arrow_lt n (by omega) f h -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the -/
/-original path. -1/ -/
/-lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) : -/
/-    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ := -/
/-  sx (n + 1) |>.spine_δ_arrow_gt n (by omega) f h -/

/-/1-- If we take the path along the spine of a face of a `spineToSimplex`, the -/
/-arrows not contained in the original path can be recovered as the diagonal edge -/
/-of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -1/ -/
/-lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) : -/
/-    (X.spine n (X.δ j (sx.spineToSimplex f))).arrow i = -/
/-      (sx (n + 1)).spineToDiagonal 2 (by omega) (f.interval i 2 (by omega)) := -/
/-  sx (n + 1) |>.spine_δ_arrow_eq n (by omega) f h -/

end StrictSegal
end SSet

open SSet Truncated

/-- Simplices in the nerve of categories are uniquely determined by their spine.
Indeed, this property describes the essential image of the nerve functor.-/
noncomputable def CategoryTheory.Nerve.strictSegal
    (C : Type u) [Category.{v} C] : StrictSegal (nerve C) := by
  intro n
  induction n with
  | zero => exact .nil _
  | succ n h =>
    refine .mk ?_ h
    exact {
    spineToSimplex F :=
      ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
        (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
          (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
    spine_spineToSimplex := by
      ext F i
      refine ComposableArrows.ext₁ ?_ ?_ ?_
      · exact Functor.congr_obj (F.arrow_src i).symm 0
      · exact Functor.congr_obj (F.arrow_tgt i).symm 0
      · dsimp [truncation, SimplicialObject.truncation]
        apply ComposableArrows.mkOfObjOfMapSucc_map_succ
    spineToSimplex_spine := by
      ext F
      fapply ComposableArrows.ext
      · intro i
        rfl
      · intro i hi
        dsimp [truncation, SimplicialObject.truncation]
        exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi }
