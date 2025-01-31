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

/-- A path of length `m` in a 0-truncated simplicial set `X` consists of `m + 1`
0-simplices in `X`. -/
@[ext]
structure Path₀ (X : SSet.Truncated.{u} 0) (m : ℕ) where
  vertex (i : Fin (m + 1)) : X _[0]₀

namespace Path₀

variable {X : SSet.Truncated.{u} 0} {m : ℕ}

/-- A 0-simplex in `X` defines a path of length 0 in `X`. -/
def of_vertex (Δ : X _[0]₀) :  Path₀ X 0 :=
  { vertex _ := Δ }

instance {X : SSet.Truncated.{u} 0} : Coe (X _[0]₀) (Path₀ X 0) where
  coe := Path₀.of_vertex

def interval (f : Path₀ X m) (j l : ℕ) (h : j + l ≤ m := by omega) :
    Path₀ X l where
  vertex i := f.vertex ⟨j + i, by omega⟩

@[simps]
def map {X Y : SSet.Truncated 0} {m : ℕ} (f : Path₀ X m) (σ : X ⟶ Y) :
    Path₀ Y m where
  vertex i := σ.app (op [0]₀) (f.vertex i)

end Path₀

/-- A path of length `m` in a 1-truncated simplicial set `X` is a directed path
of `m` edges. -/
@[ext]
structure Path₁ (X : SSet.Truncated.{u} 1) (m : ℕ)
    extends Path₀ ((trunc 1 0).obj X) m where
  arrow (i : Fin m) : X _[1]₁
  arrow_src (i : Fin m) : X.map (tr (δ 1)).op (arrow i) = vertex i.castSucc
  arrow_tgt (i : Fin m) : X.map (tr (δ 0)).op (arrow i) = vertex i.succ

namespace Path₁

variable {X : SSet.Truncated.{u} 1} {m : ℕ}

instance : Coe (Path₁ X 0) (Path₀ ((trunc 1 0).obj X) 0) where
  coe := Path₁.toPath₀

@[ext]
lemma ext' {f g : Path₁ X (m + 1)} (h : ∀ i, f.arrow i = g.arrow i) :
    f = g := by
  ext j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, hk⟩ | hl
    · rw [hk, ← f.arrow_src k, ← g.arrow_src k, h]
    · simp only [hl, ← Fin.succ_last]
      rw [← f.arrow_tgt (Fin.last m), ← g.arrow_tgt (Fin.last m), h]
  · exact h j

def interval (f : Path₁ X m) (j l : ℕ) (h : j + l ≤ m := by omega) :
    Path₁ X l where
  vertex := Path₀.interval f.toPath₀ j l h |>.vertex
  arrow i := f.arrow ⟨j + i, by omega⟩
  arrow_src i := f.arrow_src ⟨j + i, by omega⟩
  arrow_tgt i := f.arrow_tgt ⟨j + i, by omega⟩

@[simps]
def map {X Y : SSet.Truncated 1} {m : ℕ} (f : Path₁ X m) (σ : X ⟶ Y) :
    Path₁ Y m where
  vertex := Path₀.map f.toPath₀ ((trunc 1 0).map σ) |>.vertex
  arrow i := σ.app (op [1]₁) (f.arrow i)
  arrow_src i := by
    simp only [← f.arrow_src, Path₀.map_vertex]
    exact congr (σ.naturality (tr (δ 1)).op) rfl |>.symm
  arrow_tgt i := by
    simp only [← f.arrow_tgt, Path₀.map_vertex]
    exact congr (σ.naturality (tr (δ 0)).op) rfl |>.symm

end Path₁

def Path (X : SSet.Truncated.{u} n) := by
  induction n with
  | zero => exact Path₀ X
  | succ n => exact Path₁ ((trunc (n + 1) 1).obj X)

/-- Any path can be coerced to `Path₀` by forgetting the arrows. -/
instance {X : SSet.Truncated.{u} n} {m : ℕ} :
    Coe (Path X m) (Path₀ ((trunc n 0).obj X) m) where
  coe f :=
    match n with
    | .zero => f
    | .succ _ => f.toPath₀

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
  Path₀.vertex f i

def arrow {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    ((trunc (n + 1) 1).obj X) _[1]₁ :=
  Path₁.arrow f i

lemma arrow_src {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    X.map (tr (δ 1)).op (f.arrow i) = f.vertex i.castSucc :=
  Path₁.arrow_src f i

lemma arrow_tgt {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} (f : Path X m) (i : Fin m) :
    X.map (tr (δ 0)).op (f.arrow i) = f.vertex i.succ :=
  Path₁.arrow_tgt f i

/- abbrev foo {X : SSet.Truncated.{u} n} {m : ℕ} -/
/-     (f : Path X m) (j : ℕ) (h : j ≤ n) : Path ((trunc n j).obj X) m := by -/
/-   induction n with -/
/-   | zero => exact Nat.eq_zero_of_le_zero h |>.symm ▸ f -/
/-   | succ n => -/
/-     induction m with -/
/-     | zero => -/
/-       simp [Path] at f ⊢ -/
/-       exact f -/
/-     | succ m => -/
/-       simp [Path] -/
/-       exact f -/

@[ext]
lemma ext₀ {X : SSet.Truncated.{u} 0} {m : ℕ} {f g : Path X m}
    (h : f.vertex = g.vertex) : f = g :=
  Path₀.ext h

@[ext]
lemma ext₁ {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X m}
    (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) : f = g :=
  Path₁.ext hᵥ hₐ

@[ext]
lemma ext' {X : SSet.Truncated.{u} (n + 1)} {m : ℕ} {f g : Path X (m + 1)}
    (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Path₁.ext' h

def interval {X : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m)
    (j l : ℕ) (h : j + l ≤ m := by omega) : Path X l :=
  match n with
  | .zero => Path₀.interval f j l h
  | .succ _ => Path₁.interval f j l h

def map {X Y : SSet.Truncated.{u} n} {m : ℕ} (f : Path X m) (σ : X ⟶ Y) :
    Path Y m :=
  match n with
  | .zero => Path₀.map f σ
  | .succ n => Path₁.map f ((trunc (n + 1) 1).map σ)

@[simp]
lemma map_vertex {X Y : SSet.Truncated.{u} n} {m : ℕ}
    (f : Path X m) (σ : X ⟶ Y) (i : Fin (m + 1)) :
    (f.map σ).vertex i = σ.app (op [0]ₙ) (f.vertex i) :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

@[simp]
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
  /- | .zero => -/
  /-   match m with -/
  /-   | .zero => { vertex _ := Δ } -/
  /-   | .succ m => False.elim <| Nat.not_succ_le_zero m h -/
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
    (X.spine m _ Δ).vertex i = X.map (tr (const [0] [m] i)).op Δ :=
  match n with
  | .zero => rfl
    /- match m with -/
    /- | .zero => by -/
    /-   simp [Fin.eq_zero, spine, Path.vertex, tr, spine_vertex] -/
    /-   erw [CategoryTheory.op_id (X := [0]₀)] -/
    /-   simp -/
    /- | .succ m => False.elim <| Nat.not_succ_le_zero m h -/
  | .succ _ => rfl

lemma spine_arrow (X : SSet.Truncated.{u} (n + 1)) (m : ℕ) (h : m ≤ n + 1)
    (Δ : X _[m]ₙ₊₁) (i : Fin m) :
    (X.spine m _ Δ).arrow i = X.map (tr (mkOfSucc i)).op Δ :=
  rfl

lemma trunc_spine (X : SSet.Truncated.{u} (n + 1)) (j m : ℕ)
    (h : j ≤ n := by omega) (hₘ : m ≤ j + 1 := by omega) :
    ((trunc (n + 1) (j + 1)).obj X).spine m = X.spine m :=
  rfl

lemma spine_map_vertex (X : SSet.Truncated.{u} n) (m : ℕ) (hₘ : m ≤ n)
    (Δ : X _[m]ₙ) (a : ℕ) (hₐ : a ≤ n) (φ : [a]ₙ ⟶ [m]ₙ) (i : Fin (a + 1)) :
    (X.spine a hₐ (X.map φ.op Δ)).vertex i =
      (X.spine m hₘ Δ).vertex (φ.toOrderHom i) := by
  simp [spine_vertex, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
    const_comp]

lemma spine_map_subinterval (X : SSet.Truncated.{u} n)
    (m : ℕ) (hₘ : m ≤ n) (j l : ℕ) (h : j + l ≤ m) (Δ : X _[m]ₙ) :
    X.spine l (by omega) (X.map (tr (subinterval j l h)).op Δ) =
      (X.spine m hₘ Δ).interval j l h := by
  induction n
  · ext i
    rw [spine_vertex, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
      const_subinterval_eq]
    simp [Path.interval, Path₀.interval, Path.vertex, spine]
  · ext i
    · rw [spine_vertex, ← FunctorToTypes.map_comp_apply, ← op_comp,
        ← tr_comp, const_subinterval_eq]
      simp [Path.interval, Path₁.interval, Path₀.interval, Path.vertex, spine]
    · rw [spine_arrow, ← FunctorToTypes.map_comp_apply, ← op_comp, ← tr_comp,
        mkOfSucc_subinterval_eq]
      simp [Path.interval, Path₁.interval, Path₀.interval, Path.arrow, spine]

end Truncated

variable (X : SSet.{u})

/-- Unfolding the definition of `Truncated.Path`, a path of length `n + 1` in a
simplicial set `X` is defined as a `Truncated.Path₁` structure on the
1-truncation of `X`. A path of length 0 in `X` is defined as a `Truncated.Path₀`
structure on the 0-truncation of `X`. -/
abbrev Path (n : ℕ) := truncation n |>.obj X |>.Path n

namespace Path

variable {X} {n : ℕ}

/-- Constructs a `Path` of length `n` from its vertices and edges. -/
abbrev mk (vertex : Fin (n + 1) → X _[0]) (arrow : Fin n → X _[1])
    (arrow_src : ∀ i : Fin n, X.δ 1 (arrow i) = vertex i.castSucc)
    (arrow_tgt : ∀ i : Fin n, X.δ 0 (arrow i) = vertex i.succ) :
    Path X n :=
  match n with
  | .zero => { vertex := vertex }
  | .succ _ =>
    { vertex := vertex
      arrow := arrow
      arrow_src := arrow_src
      arrow_tgt := arrow_tgt }

instance : Coe (((truncation 1).obj X).Path 0) (Path X 0) where
  coe := Truncated.Path₁.toPath₀

/- instance {m : ℕ} (h : m ≤ n) : CoeOut (((truncation n).obj X).Path m) (Path X m) where -/
/-   coe f := -/
/-     match n with -/
/-     | .zero => -/
/-       match m with -/
/-       | .zero => f -/
/-       | .succ m => False.elim <| Nat.not_succ_le_zero m h -/
/-     | .succ _ => -/
/-       match m with -/
/-       | .zero => f.toPath₀ -/
/-       | .succ _ => f -/

def vertex (f : Path X n) (i : Fin (n + 1)) : X _[0] :=
  Truncated.Path.vertex f i

def arrow (f : Path X n) (i : Fin n) : X _[1] :=
  match n with
  | .zero => i.elim0
  | .succ _ => Truncated.Path.arrow f i

lemma arrow_src (f : Path X n) (i : Fin n) :
    X.δ 1 (f.arrow i) = f.vertex i.castSucc :=
  match n with
  | .zero => i.elim0
  | .succ _ => Truncated.Path.arrow_src f i

lemma arrow_tgt (f : Path X n) (i : Fin n) :
    X.δ 0 (f.arrow i) = f.vertex i.succ :=
  match n with
  | .zero => i.elim0
  | .succ _ => Truncated.Path.arrow_tgt f i

@[ext]
lemma ext {f g : Path X n} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
    f = g :=
  match n with
  | .zero => Truncated.Path.ext₀ hᵥ
  | .succ _ => Truncated.Path.ext₁ hᵥ hₐ

@[ext]
lemma ext' {f g : Path X (n + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g :=
  Truncated.Path.ext' h

def interval (f : Path X n) (j l : ℕ) (h : j + l ≤ n := by omega) : Path X l :=
  match n with
  | .zero =>
    match l with
    | .zero => Truncated.Path.interval f j 0 h
    | .succ l => False.elim <| Nat.not_succ_le_zero (j + l) h
  | .succ _ =>
    match l with
    | .zero => Truncated.Path.interval f j 0 h |>.toPath₀
    | .succ l => Truncated.Path.interval f j (l + 1) h

variable {X Y : SSet.{u}} {n : ℕ} (f : Path X n) (σ : X ⟶ Y)

/-- Maps of simplicial sets induce maps of paths. -/
def map : Path Y n :=
  Truncated.Path.map f ((truncation n).map σ)

lemma map_vertex (i : Fin (n + 1)) :
    (f.map σ).vertex i = σ.app (op [0]) (f.vertex i) :=
  match n with
  | .zero => rfl
  | .succ _ => rfl

lemma map_arrow (f : Path X (n + 1)) (i : Fin (n + 1)) :
    (f.map σ).arrow i = σ.app (op [1]) (f.arrow i) :=
  rfl

/-- `Path.map` respects subintervals of paths. -/
lemma map_interval (j l : ℕ) (h : j + l ≤ n) :
    (f.map σ).interval j l h = (f.interval j l h).map σ :=
  match n with
  | .zero =>
    match l with
    | .zero => rfl
    | .succ l => False.elim <| Nat.not_succ_le_zero (j + l) h
  | .succ _ =>
    match l with
    | .zero => rfl
    | .succ _ => rfl

end Path

def spine (n : ℕ) : X _[n] → Path X n :=
  truncation n |>.obj X |>.spine n

variable (X : SSet.{u}) (n : ℕ)

@[simp]
lemma spine_vertex (Δ : X _[n]) (i : Fin (n + 1)) :
    (X.spine n Δ).vertex i = X.map (const [0] [n] i).op Δ :=
  truncation n |>.obj X |>.spine_vertex n (by rfl) Δ i

@[simp]
lemma spine_arrow (Δ : X _[n + 1]) (i : Fin (n + 1)) :
    (X.spine (n + 1) Δ).arrow i = X.map (mkOfSucc i).op Δ :=
  rfl

end SSet
