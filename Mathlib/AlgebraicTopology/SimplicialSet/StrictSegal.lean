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

/-/1-- The data of an inverse to `X.spine n` for `X` an `n`-truncated simplicial set. -1/ -/
/-private structure StrictSegalAux0 {n : ℕ} (X : SSet.Truncated.{u} n) where -/
/-  spineToSimplex : Path X n → X _[n]ₙ -/
/-  spine_spineToSimplex : spine X n ∘ spineToSimplex = id -/
/-  spineToSimplex_spine : spineToSimplex ∘ spine X n = id -/

/-- The data of an inverse to `X.spine n` for `X` an `n`-truncated simplicial set. -/
private structure StrictSegalAux {n : ℕ} (X : SSet.Truncated.{u} n) where
  spineToSimplex : Path X n → X _[n]ₙ
  spine_spineToSimplex : spine X n ∘ spineToSimplex = id
  spineToSimplex_spine : spineToSimplex ∘ spine X n = id

/-- An `n + 1`-truncated simplicial set `X` is `StrictSegal` if its
`n + 1`-simplices are uniquely determined by their spine and its further
`n`-truncation is `StrictSegal`. -/
inductive StrictSegal : {n : ℕ} → SSet.Truncated.{u} n → Type (u + 1) where
  | nil {X : SSet.Truncated.{u} 0} : StrictSegalAux X → StrictSegal X
  | mk {n X} :
    StrictSegalAux X → StrictSegal ((trunc (n + 1) n).obj X) → StrictSegal X

namespace StrictSegal

variable {n : ℕ}

/-- For an `n`-truncated simplicial set `X` equipped with `sx : StrictSegal X`,
`sx.aux` extracts the inverse to `X.spine n`. -/
private def aux {X : SSet.Truncated.{u} n} (sx : StrictSegal X) :
    StrictSegalAux X :=
  match sx with
  | .nil aux => aux
  | .mk aux _ => aux

/-- For an `n + 1`-truncated simplicial set `X` equipped with
`sx : StrictSegal X`, `sx.next` extracts the proof that the further
`n`-truncation of `X` is `StrictSegal`. -/
private def next {X : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X) :
    StrictSegal ((trunc (n + 1) n).obj X) :=
  match sx with
  | .mk _ next => next

/-- Returns the `StrictSegal` data of the further `m`-truncation of `X`. -/
def trunc {n : ℕ} {X : SSet.Truncated n} (sx : StrictSegal X)
    (m : ℕ) (h : m ≤ n := by omega) :
    StrictSegal ((SSet.Truncated.trunc n m).obj X) :=
  if heq : m = n then
    heq.symm ▸ sx
  else
    match n with
    | .zero => False.elim <| heq <| Nat.eq_zero_of_le_zero h
    | .succ n => sx.next.trunc m

@[simp]
lemma trunc_self {n : ℕ} {X : SSet.Truncated.{u} n} (sx : StrictSegal X) :
    sx.trunc n = sx := by
  simp [trunc]

variable {X : SSet.Truncated.{u} n} (sx : StrictSegal X)

/-- The inverse to `X.spine n`. -/
def spineToSimplex : Path X n → X _[n]ₙ := sx.aux.spineToSimplex

/-- `spineToSimplex` is a right inverse to `X.spine n`. -/
def spine_spineToSimplex : spine X n ∘ spineToSimplex sx = id :=
  sx.aux.spine_spineToSimplex

/-- `spineToSimplex` is a left inverse to `X.spine n`. -/
def spineToSimplex_spine : spineToSimplex sx ∘ spine X n = id :=
  sx.aux.spineToSimplex_spine

@[simp]
lemma spine_spineToSimplex_apply (f : Path X n) :
    X.spine n _ (sx.spineToSimplex f) = f :=
  congr_fun sx.spine_spineToSimplex f

@[simp]
lemma spineToSimplex_spine_apply (Δ : X _[n]ₙ) :
    sx.spineToSimplex (X.spine n _ Δ) = Δ :=
  congr_fun sx.spineToSimplex_spine Δ

/-- The fields of `StrictSegalAux` define an equivalence between `X _[n]ₙ` and
`Path X n`. -/
def spineEquiv : X _[n]ₙ ≃ Path X n where
  toFun := spine X n
  invFun := sx.spineToSimplex
  left_inv := sx.spineToSimplex_spine_apply
  right_inv := sx.spine_spineToSimplex_apply

theorem spineInjective : Function.Injective sx.spineEquiv :=
  Equiv.injective _

/-- In the presence of the strict Segal condition, a path of length `n + 1` can
be "composed" by taking the diagonal edge of the resulting `n + 1` simplex. -/
def spineToDiagonal {X : SSet.Truncated.{u} (n + 1)} (sx : StrictSegal X) :
    Path X (n + 1) → X _[1]ₙ₊₁ :=
  X.map (tr (diag (n + 1))).op ∘ sx.spineToSimplex

@[simp]
theorem spineToSimplex_vertex {X : SSet.Truncated.{u} (n + 1)}
    (sx : StrictSegal X) (i : Fin (n + 2)) (f : Path X (n + 1)) :
    X.map (tr (const [0] [n + 1] i)).op (sx.spineToSimplex f) = f.vertex i := by
  erw [← spine_vertex X (n + 1)]
  rw [spine_spineToSimplex_apply]

@[simp]
theorem spineToSimplex_arrow {X : SSet.Truncated.{u} (n + 1)}
    (sx : StrictSegal X) (i : Fin (n + 1)) (f : Path X (n + 1)) :
    X.map (tr (mkOfSucc i)).op (sx.spineToSimplex f) = f.arrow i := by
  erw [← spine_arrow X (n + 1)]
  rw [spine_spineToSimplex_apply]

end StrictSegal


/-section interval -/

/-variable (f : Path X (n + 1)) (j l : ℕ) (h : j + l ≤ n) -/

/-@[simp] -/
/-theorem spineToSimplex_interval : -/
/-    X.map (tr (subinterval j (l + 1) (by omega))).op (sx.spineToSimplex f) = -/
/-      (sx.trunc (l + 1)).spineToSimplex (f.interval j (l + 1) (by omega)) := by -/
/-  apply sx.trunc (l + 1) |>.spineInjective -/
/-  dsimp only [spineEquiv, Equiv.coe_fn_mk] -/
/-  rw [spine_spineToSimplex_apply, trunc_spine X l (l + 1), -/
/-    spine_map_subinterval, spine_spineToSimplex_apply sx f] -/

/-theorem spineToSimplex_edge : -/
/-    X.map (tr (intervalEdge j (l + 1) (by omega))).op (sx.spineToSimplex f) = -/
/-      (sx.trunc (l + 1)).spineToDiagonal (f.interval j (l + 1) (by omega)) := by -/
/-  dsimp only [spineToDiagonal, Function.comp_apply] -/
/-  rw [← spineToSimplex_interval (h := h)] -/
/-  dsimp only [len_mk, Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, Truncated.trunc, -/
/-    SimplicialObject.Truncated.trunc, incl, whiskeringLeft_obj_obj, Functor.comp_map, -/
/-    Functor.op_obj, Functor.op_map, Quiver.Hom.unop_op] -/
/-  rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp (n := n + 1), -/
/-    ← diag_subinterval_eq] -/

/-end interval -/

/-section spine_δ -/

/-variable (f : Path X (n + 1)) {i : Fin (n + 1)} {j : Fin (n + 2)} -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-the common vertices will agree with those of the original path `f`. In particular, -/
/-a vertex `i` with `i < j` can be identified with the same vertex in `f`. -1/ -/
/-lemma spine_δ_vertex_lt (hij : i.castSucc < j) : -/
/-    (X.spine n _ (X.map (tr (δ j)).op (sx.spineToSimplex f))).vertex i = -/
/-      f.vertex i.castSucc := by -/
/-  rw [spine_vertex X n, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, -/
/-    const_comp, spineToSimplex_vertex] -/
/-  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply, -/
/-    OrderEmbedding.toOrderHom_coe] -/
/-  rw [Fin.succAbove_of_castSucc_lt j i hij] -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-a vertex `i` with `j ≤ i` can be identified with vertex `i + 1` in the original -/
/-path. -1/ -/
/-lemma spine_δ_vertex_ge (hij : j ≤ i.castSucc) : -/
/-    (X.spine n _ (X.map (tr (δ j)).op (sx.spineToSimplex f))).vertex i = -/
/-      f.vertex i.succ := by -/
/-  rw [spine_vertex X n, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, -/
/-    const_comp, spineToSimplex_vertex] -/
/-  dsimp only [δ, len_mk, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb_apply, -/
/-    OrderEmbedding.toOrderHom_coe] -/
/-  rw [Fin.succAbove_of_le_castSucc j i hij] -/

/-variable {i : Fin n} {j : Fin (n + 2)} -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-the common arrows will agree with those of the original path `f`. In particular, -/
/-an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -1/ -/
/-lemma spine_δ_arrow_lt (hij : i.succ.castSucc < j) : -/
/-    (X.spine n _ (X.map (tr (δ j)).op (sx.spineToSimplex f))).arrow i = -/
/-      f.arrow i.castSucc := by -/
/-  rw [spine_arrow X n, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, -/
/-    mkOfSucc_δ_lt hij, spineToSimplex_arrow] -/

/-/1-- If we take the path along the spine of the `j`th face of a `spineToSimplex`, -/
/-an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the -/
/-original path. -1/ -/
/-lemma spine_δ_arrow_gt (hij : j < i.succ.castSucc) : -/
/-    (X.spine n _ (X.map (tr (δ j)).op (sx.spineToSimplex f))).arrow i = -/
/-      f.arrow i.succ := by -/
/-  rw [spine_arrow X n, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, -/
/-    mkOfSucc_δ_gt hij, spineToSimplex_arrow] -/

/-end spine_δ -/

/-variable {X : SSet.Truncated.{u} (n + 2)} (sx : StrictSegal X) -/
/-  (f : Path X (n + 2)) {i : Fin (n + 1)} {j : Fin (n + 3)} -/

/-/1-- If we take the path along the spine of a face of a `spineToSimplex`, the -/
/-arrows not contained in the original path can be recovered as the diagonal edge -/
/-of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -1/ -/
/-lemma spine_δ_arrow_eq (hij : j = i.succ.castSucc) : -/
/-    (X.spine (n + 1) _ (X.map (tr (δ j)).op (sx.spineToSimplex f))).arrow i = -/
/-      (sx.trunc 2).spineToDiagonal (f.interval i 2 (by omega)) := by -/
/-  rw [spine_arrow X (n + 1), ← FunctorToTypes.map_comp_apply, ← op_comp, -/
/-    ← tr_comp, mkOfSucc_δ_eq hij, spineToSimplex_edge (h := by omega)] -/

/-end StrictSegal -/
end Truncated

variable (X : SSet.{u})

/-- A simplicial set `X` is `SSet.StrictSegal` if the `n + 1`-truncation of `X`
is `SSet.Truncated.StrictSegal` for all `n : ℕ` and this data is sufficiently
compatible. -/
abbrev StrictSegal :=
  { segal : ∀ n : ℕ, ((truncation n).obj X).StrictSegal //
    ∀ n : ℕ, (segal (n + 1)).next = segal n }

namespace StrictSegal

variable {X} (sx : StrictSegal X) {n : ℕ}

lemma trunc_eq (n m : ℕ) (h : m ≤ n) : (sx.1 n).trunc m h = sx.1 m := by
  induction n with
  | zero =>
    have := Nat.eq_zero_of_le_zero h
    subst this
    rfl
  | succ n ih =>
    by_cases heq : m = n + 1
    · subst heq
      simp [Truncated.StrictSegal.trunc]
    · dsimp [Truncated.StrictSegal.trunc]
      simp only [reduceDIte, heq, sx.2]
      exact ih (by omega)

/- instance : Coe (Path X n) (((truncation n).obj X).Path n) where -/
/-   coe f := -/
/-     match n with -/
/-     | .zero => f.toPath₀ -/
/-     | .succ _ => f -/

  /- X.Path n : Type u -/
  /- ((truncation n).obj X).Path n : Type u -/
/-- The inverse to `X.spine`. -/
/- def spineToSimplex (f : Path X n) : X _[n] := sx.1 n |>.spineToSimplex f -/
def spineToSimplex (f : Path X n) : X _[n] :=
  match n with
  | .zero => sx.1 0 |>.spineToSimplex f.toPath₀
  | .succ n => sx.1 (n + 1) |>.spineToSimplex f
  /- match n with -/
  /- | .zero => f.vertex 0 -/
  /- | .succ n => sx.1 (n + 1) |>.spineToSimplex f -/

/-- `spineToSimplex` is a right inverse to `X.spine`. -/
lemma spine_spineToSimplex : X.spine n ∘ sx.spineToSimplex = id := by
  induction n with
  | zero =>
    ext f j
    · simp only [spine, spineToSimplex, Function.comp_apply, Fin.eq_zero,
        Truncated.StrictSegal.spine_spineToSimplex_apply, Path.foo]
      simp [Truncated.Path.vertex]
    · exact j.elim0
  | succ n => exact sx.1 (n + 1) |>.spine_spineToSimplex

/-- `spineToSimplex` is a left inverse to `X.spine`. -/
lemma spineToSimplex_spine : sx.spineToSimplex ∘ X.spine (n := n) = id :=
  match n with
  | .zero => by
    ext Δ
    simp [spineToSimplex, spine]
  | .succ n => sx.1 (n + 1) |>.spineToSimplex_spine

lemma spine_spineToSimplex_apply (f : Path X n) :
    X.spine n (sx.spineToSimplex f) = f := by
  induction n with
  | zero => simp [spine, spineToSimplex]
  | succ n => exact sx.1 (n + 1) |>.spine_spineToSimplex_apply f

lemma spineToSimplex_spine_apply (Δ : X _[n]) :
    sx.spineToSimplex (X.spine n Δ) = Δ := by
  induction n with
  | zero => simp [spine, spineToSimplex]
  | succ n => exact sx.1 (n + 1) |>.spineToSimplex_spine_apply Δ

abbrev spineEquiv {n : ℕ} : X _[n] ≃ Path X n :=
  match n with
  | .zero => {
      toFun := ((truncation 1).obj X).spine 0
      invFun := (sx.1 0).spineToSimplex
  }
  | .succ n => sx.1 (n + 1) |>.spineEquiv

theorem spineInjective : Function.Injective (sx.spineEquiv (n := n)) :=
  sx.1 (n + 1) |>.spineInjective

lemma spineEquiv_coe_fn (n : ℕ) : ⇑(sx.spineEquiv (n := n)) = X.spine := rfl

lemma spineEquiv_symm_coe_fn (n : ℕ) :
    ⇑(sx.spineEquiv (n := n)).symm = sx.spineToSimplex :=
  rfl

theorem spineToSimplex_vertex (i : Fin (n + 2)) (f : Path X (n + 1)) :
    X.map (const [0] [n + 1] i).op (sx.spineToSimplex f) = f.vertex i :=
  sx.1 (n + 1) |>.spineToSimplex_vertex i f

theorem spineToSimplex_arrow (i : Fin (n + 1)) (f : Path X (n + 1)) :
    X.map (mkOfSucc i).op (sx.spineToSimplex f) = f.arrow i :=
  sx.1 (n + 1) |>.spineToSimplex_arrow i f

/-- In the presence of the strict Segal condition, a path of length `n + 1` can
be "composed" by taking the diagonal edge of the resulting `n + 1`-simplex. -/
abbrev spineToDiagonal : Path X (n + 1) → X _[1] :=
  sx.1 (n + 1) |>.spineToDiagonal

lemma spineToDiagonal_def :
    sx.spineToDiagonal = X.map (diag (n + 1)).op ∘ sx.spineToSimplex := rfl

section interval

variable (f : Path X (n + 1)) (j l : ℕ) (h : j + l ≤ n)

@[simp]
theorem spineToSimplex_interval :
    X.map (subinterval j (l + 1) (by omega)).op (sx.spineToSimplex f) =
      sx.spineToSimplex (f.interval j (l + 1) (by omega)) := by
  dsimp only [spineToSimplex]
  rw [← trunc_eq sx (n + 1) (l + 1) (by omega)]
  exact sx.1 (n + 1) |>.spineToSimplex_interval f j l h

theorem spineToSimplex_edge :
    X.map (intervalEdge j (l + 1) (by omega)).op (sx.spineToSimplex f) =
      sx.spineToDiagonal (f.interval j (l + 1) (by omega)) := by
  dsimp only [spineToDiagonal]
  rw [← trunc_eq sx (n + 1) (l + 1) (by omega)]
  exact sx.1 (n + 1) |>.spineToSimplex_edge f j l h

end interval

variable (f : Path X (n + 2))
variable {i : Fin (n + 2)} {j : Fin (n + 3)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common vertices will agree with those of the original path `f`. In particular,
a vertex `i` with `i < j` can be identified with the same vertex in `f`. -/
lemma spine_δ_vertex_lt (h : i.castSucc < j) :
    (X.spine (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.castSucc :=
  sx.1 (n + 2) |>.spine_δ_vertex_lt f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
a vertex `i` with `i ≥ j` can be identified with vertex `i + 1` in the original
path. -/
lemma spine_δ_vertex_ge (h : j ≤ i.castSucc) :
    (X.spine (X.δ j (sx.spineToSimplex f))).vertex i = f.vertex i.succ :=
  sx.1 (n + 2) |>.spine_δ_vertex_ge f h

variable {i : Fin (n + 1)} {j : Fin (n + 3)}

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
the common arrows will agree with those of the original path `f`. In particular,
an arrow `i` with `i + 1 < j` can be identified with the same arrow in `f`. -/
lemma spine_δ_arrow_lt (h : i.succ.castSucc < j) :
    (X.spine (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.castSucc :=
  sx.1 (n + 2) |>.spine_δ_arrow_lt f h

/-- If we take the path along the spine of the `j`th face of a `spineToSimplex`,
an arrow `i` with `i + 1 > j` can be identified with arrow `i + 1` in the
original path. -/
lemma spine_δ_arrow_gt (h : j < i.succ.castSucc) :
    (X.spine (X.δ j (sx.spineToSimplex f))).arrow i = f.arrow i.succ :=
  sx.1 (n + 2) |>.spine_δ_arrow_gt f h

/-- If we take the path along the spine of a face of a `spineToSimplex`, the
arrows not contained in the original path can be recovered as the diagonal edge
of the `spineToSimplex` that "composes" arrows `i` and `i + 1`. -/
lemma spine_δ_arrow_eq (h : j = i.succ.castSucc) :
    (X.spine (X.δ j (sx.spineToSimplex f))).arrow i =
      sx.spineToDiagonal (f.interval i 2 (by omega)) := by
  dsimp only [spineToDiagonal]
  rw [← trunc_eq sx (n + 2) 2]
  exact sx.1 (n + 2) |>.spine_δ_arrow_eq f h

end StrictSegal
end SSet

open SSet Truncated

/- TODO: provide an alternative constructor for `SSet.StrictSegal`. -/
/-- Simplices in the nerve of categories are uniquely determined by their spine.
Indeed, this property describes the essential image of the nerve functor.-/
noncomputable def CategoryTheory.Nerve.strictSegal
    (C : Type u) [Category.{v} C] : StrictSegal (nerve C) := by
  refine ⟨?_, ?_⟩
  · intro n
    induction n with
    | zero => exact .nil _
    | succ n h =>
      refine .mk ?_ h
      use fun F ↦
        ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
          (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
            (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0))
      · ext F i
        refine ComposableArrows.ext₁ ?_ ?_ ?_
        · exact Functor.congr_obj (F.arrow_src i).symm 0
        · exact Functor.congr_obj (F.arrow_tgt i).symm 0
        · dsimp [truncation, SimplicialObject.truncation]
          apply ComposableArrows.mkOfObjOfMapSucc_map_succ
      · ext F
        fapply ComposableArrows.ext
        · intro i
          rfl
        · intro i hi
          dsimp [truncation, SimplicialObject.truncation]
          exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi
  · intro n
    rfl
