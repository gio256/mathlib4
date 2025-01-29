/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou, Nick Ward
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Paths in simplicial sets

A path in a simplicial set `X` of length `n` is a directed path comprised of
`n + 1` 0-simplices and `n` 1-simplices, together with identifications between
0-simplices and the sources and targets of the 1-simplices. We define this
construction first for 1-truncated simplicial sets in `SSet.Truncated.Path₁`.
A path in a simplicial set `X` is then defined as a 1-truncated path in the
1-truncation of `X`.

An `n`-simplex has a maximal path, the `spine` of the simplex, which is a path
of length `n`.
-/

universe v u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet
namespace Truncated

open SimplexCategory.Truncated Hom SimplicialObject.Truncated

variable {n : ℕ}

@[ext]
structure Path₀ (X : SSet.Truncated.{u} 0) (m : ℕ) where
  vertex (i : Fin (m + 1)) : X _[0]₀

def Path₀.of_vertex {X : SSet.Truncated.{u} 0} (Δ : X _[0]₀) :  Path₀ X 0 :=
  { vertex _ := Δ }

instance (X : SSet.Truncated.{u} 0) : Coe (X _[0]₀) (Path₀ X 0) where
  coe := Path₀.of_vertex

@[ext]
structure Path₁ (X : SSet.Truncated.{u} 1) (m : ℕ) extends Path₀ ((trunc 1 0).obj X) m where
  arrow (i : Fin m) : X _[1]₁
  arrow_src (i : Fin m) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin m) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

/- instance (X : SSet.Truncated.{u} 0) : Coe (X _[0]₀) (Path₁ X 0) where -/
/-   coe f := { -/
/-     vertex _ := f -/
/-     arrow i := i.elim0 -/
/-     arrow_src i := i.elim0 -/
/-     arrow_tgt i := i.elim0 } -/

def Path (X : SSet.Truncated.{u} n) := by
  induction n with
  | zero => exact Path₀ X
  | succ n => exact Path₁ ((trunc (n + 1) 1).obj X)

/- @[ext] -/
/- structure Path₀ (X : SSet.Truncated.{u} n) (m : ℕ) where -/
/-   vertex (i : Fin (m + 1)) : ((trunc n 0).obj X) _[0]₀ -/

/- @[ext] -/
/- structure Path₁ (X : SSet.Truncated.{u} (n + 1)) (m : ℕ) extends Path₀ X m where -/
/-   arrow (i : Fin m) : ((trunc (n + 1) 1).obj X) _[1]₁ -/
/-   arrow_src (i : Fin m) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc -/
/-   arrow_tgt (i : Fin m) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ -/

/- def Path (X : SSet.Truncated.{u} n) := by -/
/-   induction n with -/
/-   | zero => exact Path₀ X -/
/-   | succ n => exact Path₁ X -/

namespace Path

def vertex {X : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) (i : Fin (m + 1)) :
    ((trunc n 0).obj X) _[0]₀ :=
  match n with
  | .zero => Path₀.vertex f i
  | .succ _ => Path₀.vertex f.toPath₀ i

def arrow {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    ((trunc (n + 1) 1).obj X) _[1]₁ :=
  Path₁.arrow f i

lemma arrow_src {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    X.map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc :=
  Path₁.arrow_src f i

lemma arrow_tgt {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    X.map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ :=
  Path₁.arrow_tgt f i

@[ext]
lemma ext₀ {X : SSet.Truncated 0} {m : ℕ} {f g : Path X m}
    (h : f.vertex = g.vertex) : f = g :=
  Path₀.ext h

@[ext]
lemma ext₁ {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X m}
    (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) : f = g :=
  Path₁.ext hᵥ hₐ

@[ext]
lemma ext {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X (m + 1)}
    (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m), ← g.arrow_tgt (Fin.last m), h]
  · exact h j

def interval {X : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m)
    (j l : ℕ) (h : j + l ≤ m := by omega) : Path X l :=
  match n with
  | .zero => { vertex i := f.vertex ⟨j + i, by omega⟩ }
  | .succ n => {
      vertex i := f.vertex ⟨j + i, by omega⟩
      arrow i := f.arrow ⟨j + i, by omega⟩
      arrow_src i := f.arrow_src ⟨j + i, by omega⟩
      arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩ }

def map {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) (σ : X ⟶ Y) : Path Y m :=
  match n with
  | .zero => { vertex i := σ.app (op [0]₀) (f.vertex i) }
  | .succ n => {
      vertex i := σ.app (op [0]ₙ₊₁) (f.vertex i)
      arrow i := σ.app (op [1]ₙ₊₁) (f.arrow i)
      arrow_src i := by
        simp only [← f.arrow_src i]
        exact congr (σ.naturality (tr (δ 1)).op) rfl |>.symm
      arrow_tgt i := by
        simp only [← f.arrow_tgt i]
        exact congr (σ.naturality (tr (δ 0)).op) rfl |>.symm }

lemma map_vertex {X Y : SSet.Truncated.{u} n} {m : ℕ}
    (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1)) :
    (f.map σ).vertex i = σ.app (op [0]ₙ) (f.vertex i) :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

lemma map_arrow {X Y : SSet.Truncated.{u} (n + 1)} {m : ℕ}
    (f : Path X m) (σ : X ⟶ Y) (i : Fin m) :
    (f.map σ).arrow i = σ.app (op [1]ₙ₊₁) (f.arrow i) :=
  rfl

lemma map_interval {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m)
    (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

end Path

def spine (X : SSet.Truncated.{u} n) (m : ℕ) (h : m ≤ n := by omega) (Δ : X _[m]ₙ) :
    Path X m :=
  match n with
  | .zero => { vertex i := X.map (tr (const [0] [m] i)).op Δ }
  | .succ _ => {
      vertex i := X.map (tr (const [0] [m] i)).op Δ
      arrow i := X.map (tr (mkOfSucc i)).op Δ
      arrow_src i := by
        dsimp only [tr, trunc, SimplicialObject.Truncated.trunc, incl,
          whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
          Quiver.Hom.unop_op]
        rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
          δ_one_mkOfSucc, Fin.coe_castSucc, Fin.coe_eq_castSucc]
      arrow_tgt i := by
        dsimp only [tr, trunc, SimplicialObject.Truncated.trunc, incl,
          whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
          Quiver.Hom.unop_op]
        rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
          δ_zero_mkOfSucc] }

lemma spine_vertex (X : SSet.Truncated.{u} n) (m : ℕ) (h : m ≤ n)
    (Δ : X _[m]ₙ) (i : Fin (m + 1)) :
    (X.spine m _ Δ).vertex i = X.map (const [0] [m] i).op Δ :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

lemma spine_arrow (X : SSet.Truncated.{u} (n + 1)) (m : ℕ) (h : m ≤ n + 1)
    (Δ : X _[m]ₙ₊₁) (i : Fin m) :
    (X.spine m _ Δ).arrow i = X.map (mkOfSucc i).op Δ :=
  rfl

/- lemma trunc_spine (X : SSet.Truncated.{u} n) (j m : ℕ) (h : j ≤ n) (hₘ : m ≤ j) : -/
/-     ((trunc n j).obj X).spine m = X.spine m := -/
/-   rfl -/

lemma spine_map_vertex (X : SSet.Truncated.{u} n) (m : ℕ) (hₘ : m ≤ n)
    (Δ : X _[m]ₙ) (a : ℕ) (hₐ : a ≤ n) (φ : [a]ₙ ⟶ [m]ₙ) (i : Fin (a + 1)) :
    (X.spine a hₐ (X.map φ.op Δ)).vertex i =
      (X.spine m hₘ Δ).vertex (φ.toOrderHom i) := by
  simp only [spine_vertex]
  rw [← FunctorToTypes.map_comp_apply]
  erw [← op_comp]
  rw [← tr_comp, const_comp]
  rfl

lemma spine_map_subinterval (X : SSet.Truncated.{u} n)
    (m : ℕ) (hₘ : m ≤ n) (j l : ℕ) (h : j + l ≤ m) (Δ : X _[m]ₙ) :
    X.spine l (by omega) (X.map (tr (subinterval j l h)).op Δ) =
      (X.spine m hₘ Δ).interval j l h := by
  induction n with
  | zero =>
    ext i
    simp only [spine_vertex]
    rw [← FunctorToTypes.map_comp_apply]
    erw [← op_comp]
    rw [← tr_comp, const_subinterval_eq]
    rfl
  | succ n =>
    ext i
    · simp only [spine_vertex]
      rw [← FunctorToTypes.map_comp_apply]
      erw [← op_comp]
      rw [← tr_comp, const_subinterval_eq]
      rfl
    · simp only [spine_arrow]
      rw [← FunctorToTypes.map_comp_apply]
      erw [← op_comp]
      rw [← tr_comp, mkOfSucc_subinterval_eq]
      rfl

end Truncated

variable (X : SSet.{u})

abbrev Path (n : ℕ) := truncation 1 |>.obj X |>.Path n
/- abbrev Path (n : ℕ) := truncation n |>.obj X |>.Path n -/
/- def Path (n : ℕ) := -/
/-   match n with -/
/-   | .zero => truncation 0 |>.obj X |>.Path 0 -/
/-   | .succ n => truncation 1 |>.obj X |>.Path (n + 1) -/

namespace Path

variable {X}

def of_path₀ (f : Truncated.Path₀ ((truncation 0).obj X) 0) : Path X 0 where
  vertex i := f.vertex i
  arrow i := i.elim0
  arrow_src i := i.elim0
  arrow_tgt i := i.elim0

instance : Coe (Truncated.Path ((truncation 0).obj X) 0) (Path X 0) where
  coe := of_path₀

@[simp]
lemma baz : Truncated.Path₁.toPath₀ ∘ of_path₀ (X := X) = id := rfl

@[simp]
lemma bar : of_path₀ (X := X) ∘ Truncated.Path₁.toPath₀ = id := by
  ext f j
  · rfl
  · exact j.elim0

@[simp]
lemma bar_apply (f : Truncated.Path₁ ((truncation 1).obj X) 0) : 
    of_path₀ f.toPath₀ = f := by
  ext j
  · rfl
  · exact j.elim0

@[simp]
lemma baz_apply (f : Truncated.Path₀ ((truncation 0).obj X) 0) :
    (of_path₀ f).toPath₀ = f :=
  rfl

@[simp]
lemma foo (f : Truncated.Path₀ ((truncation 0).obj X) 0) :
    (of_path₀ f).vertex 0 = f.vertex 0 :=
  rfl

open SimplicialObject.Truncated in
def of_vertex (X : SSet.{u}) : ((truncation 0).obj X) _[0]₀ → Path X 0 :=
  of_path₀ ∘ Truncated.Path₀.of_vertex

variable {n : ℕ}

@[ext]
lemma ext {f g : Path X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Truncated.Path.ext h

abbrev interval (f : Path X n) (j l : ℕ) (h : j + l ≤ n := by omega) : Path X l :=
  Truncated.Path.interval f j l h
  /- match n with -/
  /- | .zero => sorry -/
  /- | .succ n => Truncated.Path.interval f j l h -/

variable {X Y : SSet.{u}} {n : ℕ} (f : Path X n) (σ : X ⟶ Y)

/-- Maps of simplicial sets induce maps of paths. -/
abbrev map : Path Y n := Truncated.Path.map f ((truncation 1).map σ)
/- def map : Path Y n := Truncated.Path.map f ((truncation 1).map σ) -/
  /- induction n with -/
  /- | zero => -/
  /-   refine Truncated.Path.map ?_ ((truncation 0).map σ) -/
  /-   exact f -/
  /- | succ n => -/
  /-   refine Truncated.Path.map ?_ ((truncation 1).map σ) -/
  /-   exact f -/

lemma map_vertex (i : Fin (n + 1)) :
    (f.map σ).vertex i = σ.app (op [0]) (f.vertex i) :=
  rfl

lemma map_arrow (i : Fin n) :
    (f.map σ).arrow i = σ.app (op [1]) (f.arrow i) :=
  rfl

/-- `Path.map` respects subintervals of paths. -/
lemma map_interval (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

def spine (n : ℕ) : X _[n] → Path X n :=
  match n with
  | .zero => Path.of_path₀ ∘ ((truncation 0).obj X).spine 0
  /- | .zero => Path.of_vertex -/
  | .succ n => truncation (n + 1) |>.obj X |>.spine (n + 1)

end SSet
