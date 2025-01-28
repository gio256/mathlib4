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
structure Path₀ (X : SSet.Truncated.{u} n) (m : ℕ) where
  vertex (i : Fin (m + 1)) : ((trunc n 0).obj X) _[0]₀

@[ext]
structure Path₁ (X : SSet.Truncated.{u} (n + 1)) (m : ℕ) extends Path₀ X m where
  arrow (i : Fin m) : ((trunc (n + 1) 1).obj X) _[1]₁
  arrow_src (i : Fin m) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin m) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

def Path (X : SSet.Truncated.{u} n) := by
  induction n with
  | zero => exact Path₀ X
  | succ n => exact Path₁ X

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
lemma ext {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f g : Path X m)
    (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) : f = g :=
  Path₁.ext hᵥ hₐ

@[ext]
lemma ext' {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X (m + 1)}
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

lemma map_interval {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m)
    (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

end Path

def Path (X : SSet.Truncated.{u} n) (m : ℕ) := by
  induction m with
  | zero => exact Path₀ X 0
  | succ m =>
    induction n with
    | zero => exact ULift Empty
    | succ n => exact Path₁ X (m + 1)

namespace Path

def vertex {X : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) (i : Fin (m + 1)) :
    ((trunc n 0).obj X) _[0]₀ :=
  match m with
  | .zero => Path₀.vertex f i
  | .succ _ =>
    match n with
    | .zero => f.down.elim
    | .succ _ => Path₀.vertex f.toPath₀ i

def arrow {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    ((trunc (n + 1) 1).obj X) _[1]₁ :=
  match m with
  | .zero => i.elim0
  | .succ _ => Path₁.arrow f i

lemma arrow_src {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    X.map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc :=
  match m with
  | .zero => i.elim0
  | .succ _ => Path₁.arrow_src f i

lemma arrow_tgt {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    X.map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ :=
  match m with
  | .zero => i.elim0
  | .succ _ => Path₁.arrow_tgt f i

@[ext]
lemma ext {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f g : Path X m)
    (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) : f = g :=
  match m with
  | .zero => Path₀.ext hᵥ
  | .succ _ => Path₁.ext hᵥ hₐ

@[ext]
lemma ext' {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X (m + 1)}
    (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m), ← g.arrow_tgt (Fin.last m), h]
  · exact h j

def interval {X : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m)
    (j l : ℕ) (h : j + l ≤ m := by omega) : Path X l := by
  induction l with
  | zero => exact { vertex _ := f.vertex j }
  | succ l =>
    induction m with
    | zero => exact False.elim <| Nat.not_succ_le_zero (j + l) h
    | succ m =>
      induction n with
      | zero => exact f.down.elim
      | succ n => exact {
          vertex i := f.vertex ⟨j + i, by omega⟩
          arrow i := f.arrow ⟨j + i, by omega⟩
          arrow_src i := f.arrow_src ⟨j + i, by omega⟩
          arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩ }

def map {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) (σ : X ⟶ Y) : Path Y m := by
  induction m with
  | zero => exact { vertex _ := σ.app (op [0]ₙ) (f.vertex 0) }
  | succ m =>
    induction n with
    | zero => exact f.down.elim
    | succ n => exact {
        vertex i := σ.app (op [0]ₙ₊₁) (f.vertex i)
        arrow i := σ.app (op [1]ₙ₊₁) (f.arrow i)
        arrow_src i := by
          simp only [← f.arrow_src i]
          exact congr (σ.naturality (tr (δ 1)).op) rfl |>.symm
        arrow_tgt i := by
          simp only [← f.arrow_tgt i]
          exact congr (σ.naturality (tr (δ 0)).op) rfl |>.symm }

lemma map_interval {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m)
    (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ := by
  induction l with
  | zero =>
    induction m with
    | zero =>
      simp only [show j = 0 from Nat.eq_zero_of_le_zero h]
      rfl
    | succ m =>
      induction n with
      | zero =>
        simp [interval, map]

      | succ m => rfl
  | succ l => rfl

variable (X : SSet.Truncated.{u} 1)

/-- A path of length `n` in a 1-truncated simplicial set `X` is a directed path
of `n` edges. -/
@[ext]
structure Path₁ (n : ℕ) where
  /-- A path includes the data of `n + 1` 0-simplices in `X`.-/
  vertex (i : Fin (n + 1)) : X _[0]₁
  /-- A path includes the data of `n` 1-simplices in `X`.-/
  arrow (i : Fin n) : X _[1]₁
  /-- The source of a 1-simplex in a path is identified with the source vertex. -/
  arrow_src (i : Fin n) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  /-- The target of a 1-simplex in a path is identified with the target vertex. -/
  arrow_tgt (i : Fin n) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

namespace Path₁

variable {X} {n : ℕ}

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path₁ X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last n), ← g.arrow_tgt (Fin.last n), h]
  · exact h j

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
def interval (f : Path₁ X n) (j l : ℕ) (h : j + l ≤ n := by omega) :
    Path₁ X l where
  vertex i := f.vertex ⟨j + i, by omega⟩
  arrow i := f.arrow ⟨j + i, by omega⟩
  arrow_src i := f.arrow_src ⟨j + i, by omega⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩

variable {X Y : SSet.Truncated.{u} 1} {n : ℕ}

/-- Maps of 1-truncated simplicial sets induce maps of paths. -/
@[simps]
def map (f : Path₁ X n) (σ : X ⟶ Y) : Path₁ Y n where
  vertex i := σ.app (op [0]₁) (f.vertex i)
  arrow i := σ.app (op [1]₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src i]
    exact congr (σ.naturality (tr (δ 1)).op) rfl |>.symm
  arrow_tgt i := by
    simp only [← f.arrow_tgt i]
    exact congr (σ.naturality (tr (δ 0)).op) rfl |>.symm

/-- `Path₁.map` respects subintervals of paths. -/
lemma map_interval (f : Path₁ X n) (σ : X ⟶ Y) (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ := rfl

end Path₁

abbrev Path₀ (X : SSet.Truncated.{u} 0) := X _[0]₀

variable {n : ℕ}

def Path (X : SSet.Truncated.{u} n) (m : ℕ) : Type u :=
  match m with
  | .zero => trunc n 0 |>.obj X |>.Path₀
  | .succ _ =>
    match n with
    | .zero => ULift Empty
    | .succ n => trunc (n + 1) 1 |>.obj X |>.Path₁ m

namespace Path

def Vertex {X : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) : Type u :=
  match m with
  | .zero => trunc n 0 |>.obj X |>.Path₀
  | .succ _ =>
    match n with
    | .zero => ULift Empty
    | .succ n => ((trunc (n + 1) 1).obj X) _[0]₁

/- def Arrow (X : SSet.Truncated.{u} (n + 1)) {m : ℕ} (f : Path X m) : Type u := -/
/-   ((trunc (n + 1) 1).obj X) _[1]₁ -/

def Arrow (X : SSet.Truncated.{u} (n + 1)) : Type u :=
  ((trunc (n + 1) 1).obj X) _[1]₁

def vertex {X : SSet.Truncated.{u} n} {m : ℕ}
    (f : Path X m) (i : Fin (m + 1)) : Vertex f :=
  match m with
  | .zero => f
  | .succ _ =>
    match n with
    | .zero => f.down.elim
    | .succ _ => Path₁.vertex f i

def arrow {X : SSet.Truncated.{u} (n + 1)} {m : ℕ}
    (f : Path X (m + 1)) (i : Fin (m + 1)) : Arrow X :=
  Path₁.arrow f i

@[ext]
lemma ext {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X (m + 1)}
    (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) : f = g :=
  Path₁.ext hᵥ hₐ

@[ext]
lemma ext' {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X (m + 1)}
    (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Path₁.ext' h

def interval {X : SSet.Truncated.{u} n} {m : ℕ}
    (f : Path X m) (j l : ℕ) (h : j + l ≤ m := by omega) : Path X l :=
  match l with
  | .zero => f.vertex j
  | .succ l => sorry


  induction n with
  | zero =>
    induction m with
    | zero =>
      induction l with
      | zero => exact f
      | succ l => exact False.elim <| Nat.not_succ_le_zero (j + l) h
    | succ m => exact f.down.elim
  | succ n => exact Path₁.interval f j l h

def map {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) (σ : X ⟶ Y) : Path Y m := by
  induction n with
  | zero =>
    induction m with
    | zero => exact σ.app (op [0]₀) f
    | succ => exact f
  | succ n => exact Path₁.map f ((trunc (n + 1) 1).map σ)

variable {X Y : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (σ : X ⟶ Y)

lemma map_vertex (i : Fin (m + 1)) :
    (f.map σ).vertex i = σ.app (op [0]ₙ₊₁) (f.vertex i) :=
  rfl

lemma map_arrow (i : Fin m) :
    (f.map σ).arrow i = σ.app (op [1]ₙ₊₁) (f.arrow i) :=
  rfl

lemma map_interval (j l : ℕ) (h : j + l ≤ m) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  rfl

end Path

def spine (X : SSet.Truncated n) (m : ℕ) (h : m ≤ n := by omega) (Δ : X _[m]ₙ) : Path X m := by
  induction n with
  | zero =>
    induction m with
    | zero => exact Δ
    | succ m => exact False.elim <| Nat.not_succ_le_zero m h
  | succ n =>
    refine {
      vertex i := X.map (tr (const [0] [m] i)).op Δ
      arrow i := X.map (tr (mkOfSucc i)).op Δ
      arrow_src i := ?_
      arrow_tgt i := ?_ }
    · dsimp only [tr, trunc, SimplicialObject.Truncated.trunc, incl,
        whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, δ_one_mkOfSucc,
        Fin.coe_castSucc, Fin.coe_eq_castSucc]
    · dsimp only [tr, trunc, SimplicialObject.Truncated.trunc, incl,
        whiskeringLeft_obj_obj, id_eq, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp, δ_zero_mkOfSucc]

variable (X : SSet.Truncated.{u} (n + 1))

/-- Further truncating `X` above `m` does not change the `m`-spine. -/
lemma trunc_spine (j m : ℕ)
    (h : m ≤ j + 1 := by omega) (hn : j ≤ n := by omega) :
    ((trunc (n + 1) (j + 1)).obj X).spine m = X.spine m :=
  rfl

lemma spine_vertex (m : ℕ) (h : m ≤ n + 1) (Δ : X _[m]ₙ₊₁) (i : Fin (m + 1)) :
    (X.spine m _ Δ).vertex i = X.map (const [0] [m] i).op Δ :=
  rfl

lemma spine_arrow (m : ℕ) (h : m ≤ n + 1) (Δ : X _[m]ₙ₊₁) (i : Fin m) :
    (X.spine m _ Δ).arrow i = X.map (mkOfSucc i).op Δ :=
  rfl

lemma spine_map_vertex (m : ℕ) (hm : m ≤ n + 1) (Δ : X _[m]ₙ₊₁)
    (a : ℕ) (ha : a ≤ n + 1) (φ : [a]ₙ₊₁ ⟶ [m]ₙ₊₁) (i : Fin (a + 1)) :
    (X.spine a ha (X.map φ.op Δ)).vertex i =
      (X.spine m hm Δ).vertex (φ.toOrderHom i) := by
  dsimp only [spine_vertex]
  rw [← FunctorToTypes.map_comp_apply]
  erw [← op_comp]
  rw [← tr_comp, const_comp]
  rfl

lemma spine_map_subinterval (m : ℕ) (h : m ≤ n + 1) (j l : ℕ) (hjl : j + l ≤ m)
    (Δ : X _[m]ₙ₊₁) :
    X.spine l (by omega) (X.map (tr (subinterval j l hjl)).op Δ) =
      (X.spine m h Δ).interval j l hjl := by
  ext i
  · dsimp [Path.interval, Path₁.interval, spine_vertex]
    rw [← FunctorToTypes.map_comp_apply]
    erw [← op_comp]
    rw [← tr_comp, const_subinterval_eq j l hjl]
    rfl
  · dsimp only [Path.interval, Path₁.interval, spine_arrow]
    rw [← FunctorToTypes.map_comp_apply]
    erw [← op_comp]
    rw [← tr_comp, mkOfSucc_subinterval_eq]
    rfl

end Truncated

variable (X : SSet.{u})

/-- A path of length `n` in a simplicial set `X` is defined by 1-truncating `X`,
then taking the 1-truncated path. -/
/- abbrev Path (n : ℕ) := truncation 1 |>.obj X |>.Path₁ n -/
/- abbrev Path (n : ℕ) := truncation n |>.obj X |>.Path n -/
def Path (n : ℕ) :=
  match n with
  | .zero => truncation 0 |>.obj X |>.Path₀
  | .succ n => truncation 1 |>.obj X |>.Path₁ (n + 1)

namespace Path
open Truncated (Path₁)

variable {X} {n : ℕ}

/-- To show two paths equal it suffices to show that they have the same edges. -/
@[ext]
lemma ext' {f g : Path X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Path₁.ext' h

/-- For `j + l ≤ n`, a path of length `n` restricts to a path of length `l`, namely
the subpath spanned by the vertices `j ≤ i ≤ j + l` and edges `j ≤ i < j + l`. -/
def interval (f : Path X n) (j l : ℕ) (h : j + l ≤ n := by omega) : Path X l :=
  match n with
  | .zero =>
  Path₁.interval f j l h

variable {X Y : SSet.{u}} {n : ℕ} (f : Path X n) (σ : X ⟶ Y)

/-- Maps of `n + 1`-truncated simplicial sets induce maps of paths. -/
abbrev map : Path Y n := Path₁.map f <| truncation 1 |>.map σ

lemma map_vertex (i : Fin (n + 1)) :
    (f.map σ).vertex i = σ.app (op [0]) (f.vertex i) := rfl

lemma map_arrow (i : Fin n) :
    (f.map σ).arrow i = σ.app (op [1]) (f.arrow i) := rfl

/-- `Path.map` respects subintervals of paths. -/
lemma map_interval (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ := rfl

end Path

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n`
formed by traversing in order through the vertices of `X _[n]ₙ`. -/
def spine {n : ℕ} : X _[n] → Path X n :=
  match n with
  | .zero => fun x ↦ {
      vertex i := x
      arrow i := i.elim0
      arrow_src i := i.elim0
      arrow_tgt i := i.elim0
    }
  | .succ n => truncation (n + 1) |>.obj X |>.spine (n + 1)

/- lemma spine_vertex {n : ℕ} (Δ : X _[n]) (i : Fin (n + 1)) : -/
/-     (X.spine Δ).vertex i = X.map (const [0] [n] i).op Δ := -/
/-   match n with -/
/-   | .zero => by -/
/-     simp [spine] -/
/-     rfl -/
/-   | .succ n => rfl -/

lemma spine_vertex {n : ℕ} (Δ : X _[n + 1]) (i : Fin (n + 2)) :
    (X.spine Δ).vertex i = X.map (const [0] [n + 1] i).op Δ := rfl

lemma spine_arrow {n : ℕ} (Δ : X _[n + 1]) (i : Fin (n + 1)) :
    (X.spine Δ).arrow i = X.map (mkOfSucc i).op Δ := rfl

/-- For `m ≤ n`, the `m`-spine of `X` factors through the `n + 1`-truncation. -/
lemma truncation_spine (n m : ℕ) (h : m ≤ n := by omega) :
    ((truncation (n + 1)).obj X).spine (m + 1) = X.spine := rfl

lemma spine_map_vertex {n : ℕ} (Δ : X _[n + 1]) {m : ℕ} (φ : [m + 1] ⟶ [n + 1])
    (i : Fin (m + 1)) :
    (spine X (X.map φ.op Δ)).vertex i =
      (spine X Δ).vertex (φ.toOrderHom i) :=
  truncation (max m n + 1) |>.obj X
    |>.spine_map_vertex (n + 1) (by omega) Δ (m + 1) (by omega) φ i

lemma spine_map_subinterval {n : ℕ} (j l : ℕ) (h : j + l ≤ n) (Δ : X _[n + 1]) :
    X.spine (X.map (subinterval j (l + 1) (by omega)).op Δ) =
      (X.spine Δ).interval j (l + 1) (by omega) :=
  truncation (n + 1) |>.obj X
    |>.spine_map_subinterval (n + 1) _ j (l + 1) (by omega) Δ

/-- The spine of the unique non-degenerate `n`-simplex in `Δ[n]`. -/
def stdSimplex.spineId (n : ℕ) : Path Δ[n + 1] (n + 1) :=
  spine Δ[n + 1] (id (n + 1))

/-- Any inner horn contains `stdSimplex.spineId`. -/
@[simps]
def horn.spineId {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path Λ[n + 2, i] (n + 2) where
  vertex j := ⟨stdSimplex.spineId _ |>.vertex j, horn.const n i j _ |>.2⟩
  arrow j := ⟨stdSimplex.spineId _ |>.arrow j, by
    let edge := primitiveEdge h₀ hₙ j
    suffices (stdSimplex.spineId _).arrow j = edge.1 from this ▸ edge.2
    dsimp only [stdSimplex.spineId, spine_arrow, stdSimplex.map_apply]
    apply EmbeddingLike.apply_eq_iff_eq _ |>.mpr
    apply Hom.ext_one_left <;> rfl⟩
  arrow_src := by
    simp only [SimplicialObject.truncation, horn, whiskeringLeft_obj_obj,
      Functor.comp_obj, Functor.comp_map, Subtype.mk.injEq]
    exact stdSimplex.spineId (n + 1) |>.arrow_src
  arrow_tgt := by
    simp only [SimplicialObject.truncation, horn, whiskeringLeft_obj_obj,
      Functor.comp_obj, Functor.comp_map, Subtype.mk.injEq]
    exact stdSimplex.spineId (n + 1) |>.arrow_tgt

@[simp]
lemma horn.spineId_map_hornInclusion {n : ℕ} (i : Fin (n + 3))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    Path.map (horn.spineId i h₀ hₙ) (hornInclusion (n + 2) i) =
      stdSimplex.spineId (n + 1) := rfl

end SSet
