import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

def P1 (A : Set X) : Prop :=
  A ⊆ closure (interior A)

def P2 (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

def P3 (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  exact Set.Subset.trans hP2 interior_subset

theorem P2_of_open {A : Set X} (h : IsOpen A) : P2 A := by
  -- Unfold the definition of `P2`
  dsimp [P2]
  intro x hxA
  -- Since `A` is open, its interior is itself
  have hx_int : x ∈ interior A := by
    simpa [h.interior_eq] using hxA
  -- Show `interior A ⊆ interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    -- `interior A` is contained in its closure
    have h_closure : interior A ⊆ closure (interior A) := by
      intro y hy
      exact subset_closure hy
    -- Use maximality of the interior
    exact interior_maximal h_closure isOpen_interior
  -- Conclude
  exact h_subset hx_int

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- Unfold the definition of `P1`
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x` comes from `A`
      have hxA : x ∈ closure (interior A) := hA hA_mem
      -- `interior A` is contained in `interior (A ∪ B)`
      have h_subset : interior A ⊆ interior (A ∪ B) := interior_mono (by
        intro y hy
        exact Or.inl hy)
      -- Hence, `x` is in the desired closure
      exact (closure_mono h_subset) hxA
  | inr hB_mem =>
      -- `x` comes from `B`
      have hxB : x ∈ closure (interior B) := hB hB_mem
      -- `interior B` is contained in `interior (A ∪ B)`
      have h_subset : interior B ⊆ interior (A ∪ B) := interior_mono (by
        intro y hy
        exact Or.inr hy)
      -- Hence, `x` is in the desired closure
      exact (closure_mono h_subset) hxB

theorem closure_eq_of_P1 {A : Set X} (hA : P1 A) : closure (interior A) = closure A := by
  apply Set.Subset.antisymm
  ·
    exact closure_mono interior_subset
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using h

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact (interior_mono (closure_mono interior_subset)) hx

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have : x ∈ interior (closure A) := by
    simpa [hA, interior_univ] using (Set.mem_univ x)
  exact this

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact h_subset hx'
  | inr hxB =>
      have hx' : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact h_subset hx'

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` belongs to `A`
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      -- Show the needed inclusion of interiors
      have h_subset : interior (closure (interior A)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_subset hx'
  | inr hxB =>
      -- `x` belongs to `B`
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      -- Show the needed inclusion of interiors
      have h_subset : interior (closure (interior B)) ⊆
                      interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_subset hx'

theorem closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P3 A) : closure A = closure (interior (closure A)) := by
  -- First, rewrite the `P3` hypothesis as an inclusion we can use.
  have h_sub : (A : Set X) ⊆ interior (closure A) := by
    simpa [Topology.P3] using hA
  -- Prove the desired equality via two inclusions.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior (closure A))`
    have : closure A ⊆ closure (interior (closure A)) := closure_mono h_sub
    simpa using this
  · -- `closure (interior (closure A)) ⊆ closure A`
    have : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono (interior_subset : interior (closure A) ⊆ closure A)
    simpa [closure_closure] using this

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  simpa using (Topology.P2_of_open (A := interior A) isOpen_interior)

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  exact Topology.P2_implies_P3 (A := A) (Topology.P2_of_open (A := A) hA)

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  exact Topology.P2_implies_P1 (Topology.P2_of_open (A := A) hA)

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  simpa using (Topology.P1_of_open (A := interior A) isOpen_interior)

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hA
    exact Topology.closure_eq_of_P1 hA
  · intro h_eq
    dsimp [Topology.P1]
    intro x hxA
    have hx_cl : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_cl

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _

theorem P2_union₃ {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  -- First, unite `A` and `B`
  have hAB : Topology.P2 (A ∪ B) := Topology.P2_union hA hB
  -- Then unite the result with `C`
  have hABC : Topology.P2 ((A ∪ B) ∪ C) := Topology.P2_union hAB hC
  -- Rewrite the union to match the goal
  simpa [Set.union_assoc] using hABC

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P1 A) : Topology.P1 (⋃₀ 𝒜) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at *
  intro x hx
  -- Obtain a set `A` from the union that contains `x`
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  -- Apply the hypothesis `h` to `A`
  have hP1A : Topology.P1 A := h A hA_mem
  -- From `P1 A`, we know `x` is in the closure of the interior of `A`
  have hx_closure_intA : x ∈ closure (interior A) := hP1A hxA
  -- Show that `interior A ⊆ interior (⋃₀ 𝒜)`
  have h_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
    -- First, note that `A ⊆ ⋃₀ 𝒜`
    have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    -- Use monotonicity of `interior`
    exact interior_mono hA_subset
  -- Therefore, `closure (interior A) ⊆ closure (interior (⋃₀ 𝒜))`
  have h_closure_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_subset
  -- Conclude
  exact h_closure_subset hx_closure_intA

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact ⟨Topology.P2_implies_P1 hP2, Topology.P2_implies_P3 hP2⟩
  · rintro ⟨hP1, hP3⟩
    dsimp [Topology.P2] at *
    intro x hxA
    have hx : x ∈ interior (closure A) := hP3 hxA
    have h_closure_eq := Topology.closure_eq_of_P1 hP1
    simpa [h_closure_eq.symm] using hx

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  have : x ∈ (Set.univ : Set X) := Set.mem_univ x
  simpa [h, interior_univ] using this

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP1i : Topology.P1 (A i) := h i
  have hx_cl : x ∈ closure (interior (A i)) := hP1i hxAi
  have h_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    -- First, show `A i ⊆ ⋃ j, A j`
    have hAi_subset : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    -- Then use monotonicity of `interior`
    exact interior_mono hAi_subset
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_subset
  exact h_closure_subset hx_cl

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P3 A) : Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := h A hA_mem
  have hx_in : x ∈ interior (closure A) := hP3A hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact h_subset hx_in

theorem P3_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure A) = Set.univ → Topology.P3 A := by
  intro h
  dsimp [Topology.P3] at *
  intro x hx
  simpa [h] using (Set.mem_univ x)

theorem P1_unionᵢ {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, interior (A i)) := by
  -- Build P1 for each interior set (mentioning `h` so it's not unused)
  have h' : ∀ i, Topology.P1 (interior (A i)) := by
    intro i
    have _ := h i
    simpa using (Topology.P1_interior (A := A i))
  simpa using
    (P1_iUnion (ι := ι) (X := X) (A := fun i => interior (A i)) h')

theorem P2_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h₁ : ∀ A ∈ 𝒜, IsOpen A) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := Topology.P2_of_open (A := A) (h₁ A hA_mem)
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_subset : interior (closure (interior A)) ⊆
                  interior (closure (interior (⋃₀ 𝒜))) := by
    have h1 : interior A ⊆ interior (⋃₀ 𝒜) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    have h2 : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h1
    exact interior_mono h2
  exact h_subset hx_in

theorem P3_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  exact Set.Subset.trans subset_closure h

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  dsimp [Topology.P1] at *
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx : x ∈ closure (interior A) := hA hxA
  -- `e` maps this point into the image of that closure
  have hx_img : (e x : Y) ∈ e '' closure (interior A) := ⟨x, hx, rfl⟩
  -- Identify the image of the closure and of the interior through `e`
  have h_closure_eq := e.image_closure (s := interior A)
  have h_interior_eq := e.image_interior (s := A)
  -- Transport membership through these equalities
  have hx_img' : (e x : Y) ∈ closure (e '' interior A) := by
    simpa [h_closure_eq] using hx_img
  have : (e x : Y) ∈ closure (interior (e '' A)) := by
    simpa [h_interior_eq] using hx_img'
  exact this

theorem P3_countable_union {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h : ∀ n, Topology.P3 (A n)) : Topology.P3 (⋃ n, A n) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨n, hxAn⟩
  have hP3n : Topology.P3 (A n) := h n
  have hx_in : x ∈ interior (closure (A n)) := hP3n hxAn
  have h_subset : interior (closure (A n)) ⊆ interior (closure (⋃ m, A m)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨n, hy⟩
  exact h_subset hx_in

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P3 B) : Topology.P3 (e ⁻¹' B) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3] at *
  intro x hx
  -- `hx` tells us that `e x ∈ B`
  have hxB : (e x : Y) ∈ B := hx
  -- Apply `hB` to obtain that `e x` lies in the interior of `closure B`
  have hx_int : (e x : Y) ∈ interior (closure B) := hB hxB
  -- We establish that `e '' (e ⁻¹' B) = B`
  have h_image_preimage : (e '' (e ⁻¹' B) : Set Y) = B := by
    ext y
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact hx'
    · intro hy
      refine ⟨e.symm y, ?_, ?_⟩
      · dsimp [Set.preimage]
        simpa [e.apply_symm_apply] using hy
      · simpa [e.apply_symm_apply]
  -- Using the previous equality, rewrite the images of closures and interiors
  have h_image_closure :
      (e '' closure (e ⁻¹' B) : Set Y) = closure B := by
    have := e.image_closure (s := (e ⁻¹' B))
    simpa [h_image_preimage] using this
  have h_image_interior :
      (e '' interior (closure (e ⁻¹' B)) : Set Y) = interior (closure B) := by
    have := e.image_interior (s := closure (e ⁻¹' B))
    simpa [h_image_closure] using this
  -- Transport the membership of `e x`
  have h_in_img : (e x : Y) ∈ e '' interior (closure (e ⁻¹' B)) := by
    simpa [h_image_interior.symm] using hx_int
  -- Extract the witness from the image membership
  rcases h_in_img with ⟨y, hy_in, hyeq⟩
  -- Injectivity of `e` gives `y = x`
  have : (y : X) = x := by
    apply e.injective
    simpa using hyeq
  -- Conclude
  simpa [this] using hy_in

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  simpa using (Topology.P3_of_open (A := interior A) isOpen_interior)

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.P2_of_open (A := A) hA
  · intro hP2
    exact Topology.P2_implies_P1 hP2

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  ·
    exact Topology.P2_implies_P3
  ·
    intro hP3
    dsimp [Topology.P2] at *
    intro x hxA
    -- From `P3` and the fact that `A` is closed, we get `x ∈ interior A`.
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using this
    -- We now show that `interior A ⊆ interior (closure (interior A))`.
    have h_subset : interior A ⊆ interior (closure (interior A)) := by
      -- First, `interior A` is contained in its closure.
      have h_cl : interior A ⊆ closure (interior A) := by
        intro y hy
        exact subset_closure hy
      -- Apply `interior_maximal`; note `interior (interior A) = interior A`.
      simpa [interior_interior] using interior_maximal h_cl isOpen_interior
    -- Conclude using the above inclusion.
    exact h_subset hx_intA

theorem P2_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP2i : Topology.P2 (A i) := h i
  have hx_in : x ∈ interior (closure (interior (A i))) := hP2i hxAi
  have h_subset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact h_subset hx_in

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod A B) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at *
  -- Take an arbitrary point `p` in `A ×ˢ B`
  intro p hp
  -- Break down the membership of `p`
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the `P1` hypotheses on the two coordinates
  have hA_cl : p.1 ∈ closure (interior A) := hA hpA
  have hB_cl : p.2 ∈ closure (interior B) := hB hpB
  -- Hence `p` lies in the product of the two closures
  have h_mem_prod :
      p ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    ⟨hA_cl, hB_cl⟩
  -- Identify this product with the closure of the product of interiors
  have h_closure_prod_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) :=
    closure_prod_eq
  have h_mem_closure_prod :
      p ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_closure_prod_eq] using h_mem_prod
  -- The product of the interiors is contained in the interior of the product
  have h_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    -- It is open …
    have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
      isOpen_interior.prod isOpen_interior
    -- … and contained in `A ×ˢ B`
    have h_sub : Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨hq1, hq2⟩
      exact And.intro (interior_subset hq1) (interior_subset hq2)
    -- Hence it lies inside the interior of the product
    exact interior_maximal h_sub h_open
  -- Take closures to pass to the desired set
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_subset
  -- Conclude
  exact h_closure_subset h_mem_closure_prod

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod A B) := by
  -- Unfold `P2`
  dsimp [Topology.P2] at *
  intro p hp
  -- Split the membership of `p`
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the hypotheses on the two coordinates
  have h1 : p.1 ∈ interior (closure (interior A)) := hA hpA
  have h2 : p.2 ∈ interior (closure (interior B)) := hB hpB
  -- `p` belongs to the following open product
  have h_mem :
      p ∈
        Set.prod (interior (closure (interior A)))
                 (interior (closure (interior B))) :=
    ⟨h1, h2⟩
  -- Show that this product is contained in
  -- `closure (interior (A ×ˢ B))`
  have h_subset :
      Set.prod (interior (closure (interior A)))
               (interior (closure (interior B))) ⊆
        closure (interior (Set.prod A B)) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Move each coordinate inside the corresponding closure
    have hq1_cl : q.1 ∈ closure (interior A) := interior_subset hq1
    have hq2_cl : q.2 ∈ closure (interior B) := interior_subset hq2
    -- Hence `q` lies in the product of the two closures
    have hq_prod :
        q ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      ⟨hq1_cl, hq2_cl⟩
    -- Identify this product with a closure of a product
    have h_prod_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) :=
      closure_prod_eq
    have hq_closure :
        q ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_prod_eq] using hq_prod
    -- `interior A ×ˢ interior B` sits inside `interior (A ×ˢ B)`
    have h_sub_prod :
        Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
      -- The product of interiors is open …
      have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
        isOpen_interior.prod isOpen_interior
      -- … and contained in `A ×ˢ B`
      have h_sub :
          Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
        intro r hr
        exact And.intro (interior_subset hr.1) (interior_subset hr.2)
      -- Apply `interior_maximal`
      exact interior_maximal h_sub h_open
    -- Take closures
    have h_closure_sub :
        closure (Set.prod (interior A) (interior B)) ⊆
          closure (interior (Set.prod A B)) :=
      closure_mono h_sub_prod
    -- Conclude the desired inclusion
    exact h_closure_sub hq_closure
  -- The product we built is open
  have h_open_prod :
      IsOpen (Set.prod (interior (closure (interior A)))
                       (interior (closure (interior B)))) :=
    isOpen_interior.prod isOpen_interior
  -- Therefore it is contained in the *interior* of the target set
  have h_sub_interior :
      Set.prod (interior (closure (interior A)))
               (interior (closure (interior B))) ⊆
        interior (closure (interior (Set.prod A B))) :=
    interior_maximal h_subset h_open_prod
  -- Apply this inclusion to `p`
  exact h_sub_interior h_mem

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod A B) := by
  -- Unfold `P3`
  dsimp [Topology.P3] at *
  intro p hp
  -- Decompose the membership of `p`
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the `P3` hypotheses on the two coordinates
  have h1 : p.1 ∈ interior (closure A) := hA hpA
  have h2 : p.2 ∈ interior (closure B) := hB hpB
  -- Hence `p` lies in the product of the two interiors
  have h_mem :
      p ∈ Set.prod (interior (closure A)) (interior (closure B)) :=
    ⟨h1, h2⟩
  -- The product of the interiors is open
  have h_open :
      IsOpen (Set.prod (interior (closure A)) (interior (closure B))) :=
    isOpen_interior.prod isOpen_interior
  -- Show that this product is contained in the closure of `A ×ˢ B`
  have h_sub_closure :
      Set.prod (interior (closure A)) (interior (closure B)) ⊆
        closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate is in the corresponding closure
    have hq1_cl : q.1 ∈ closure A := interior_subset hq1
    have hq2_cl : q.2 ∈ closure B := interior_subset hq2
    -- So `q` lies in the product of closures
    have hq_prod : q ∈ Set.prod (closure A) (closure B) :=
      ⟨hq1_cl, hq2_cl⟩
    -- Identify this set with the closure of the product
    have h_eq : closure (Set.prod A B) = Set.prod (closure A) (closure B) :=
      closure_prod_eq
    simpa [h_eq] using hq_prod
  -- By maximality of the interior, we can pass to the interior
  have h_sub_interior :
      Set.prod (interior (closure A)) (interior (closure B)) ⊆
        interior (closure (Set.prod A B)) :=
    interior_maximal h_sub_closure h_open
  -- Conclude for our point `p`
  exact h_sub_interior h_mem

theorem P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : Topology.P1 A ↔ Topology.P3 A := by
  -- Obtain `P2 A` from the density hypothesis
  have hP2 : Topology.P2 (A := A) :=
    Topology.P2_of_dense_interior (A := A) h_dense
  -- Extract `P1 A ∧ P3 A` from `P2 A`
  have hP1P3 : Topology.P1 A ∧ Topology.P3 A :=
    ((Topology.P2_iff_P1_and_P3 (A := A)).1 hP2)
  -- Build the desired equivalence
  exact
    ⟨
      -- Forward implication: `P1 A → P3 A`
      fun _ => (Topology.P2_implies_P3 (A := A) hP2),
      -- Backward implication: `P3 A → P1 A`
      fun _ => hP1P3.1
    ⟩

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  -- Unfold the definition of `P3`
  dsimp [Topology.P3] at *
  intro y hy
  -- Obtain a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply the `P3` hypothesis to `x`
  have hx : x ∈ interior (closure A) := hA hxA
  -- Map this membership through the homeomorphism
  have hx_img : (e x : Y) ∈ e '' interior (closure A) := ⟨x, hx, rfl⟩
  -- `e` transports interiors and closures
  have h_int_eq := e.image_interior (s := closure A)
  have h_cl_eq  := e.image_closure  (s := A)
  -- Rewrite the membership step by step
  have h1 : (e x : Y) ∈ interior (e '' closure A) := by
    simpa [h_int_eq] using hx_img
  have h2 : (e x : Y) ∈ interior (closure (e '' A)) := by
    simpa [h_cl_eq] using h1
  exact h2

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P2 B) : Topology.P2 (e ⁻¹' B) := by
  -- Unfold the definition of `P2`
  dsimp [Topology.P2] at hB ⊢
  -- Take an arbitrary point in `e ⁻¹' B`
  intro x hx
  -- Transport the membership through `e`
  have hxB : (e x : Y) ∈ B := by
    simpa [Set.preimage] using hx
  -- Apply the `P2` hypothesis on `B`
  have h_intB : (e x : Y) ∈ interior (closure (interior B)) := by
    have hB_sub : (B : Set Y) ⊆ interior (closure (interior B)) := by
      simpa using hB
    exact hB_sub hxB
  -- Identify the image of the preimage of `B`
  have h_image_preimage : (e '' (e ⁻¹' B) : Set Y) = B := by
    ext y
    constructor
    · rintro ⟨x', hx', rfl⟩
      simpa [Set.preimage] using hx'
    · intro hy
      refine ⟨e.symm y, ?_, ?_⟩
      · simpa [Set.preimage, e.apply_symm_apply] using hy
      · simpa [e.apply_symm_apply]
  -- Transport interiors and closures through `e`
  have h_image_interior :
      (e '' interior (e ⁻¹' B) : Set Y) = interior B := by
    simpa [h_image_preimage] using e.image_interior (s := (e ⁻¹' B))
  have h_image_closure :
      (e '' closure (interior (e ⁻¹' B)) : Set Y) = closure (interior B) := by
    simpa [h_image_interior] using
      e.image_closure (s := interior (e ⁻¹' B))
  have h_image_int_closure :
      (e '' interior (closure (interior (e ⁻¹' B))) : Set Y) =
        interior (closure (interior B)) := by
    simpa [h_image_closure] using
      e.image_interior (s := closure (interior (e ⁻¹' B)))
  -- Using the previous equality, rewrite the membership of `e x`
  have h_in_img :
      (e x : Y) ∈ e '' interior (closure (interior (e ⁻¹' B))) := by
    simpa [h_image_int_closure] using h_intB
  -- Extract the witness from the image membership
  rcases h_in_img with ⟨y, hy_in, hyeq⟩
  -- Injectivity of `e` gives `y = x`
  have : (y : X) = x := by
    apply e.injective
    simpa using hyeq
  -- Conclude
  simpa [this] using hy_in

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  dsimp [Topology.P2] at hA ⊢
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply the `P2` hypothesis on `A`
  have hx : x ∈ interior (closure (interior A)) := hA hxA
  -- Transport this membership through `e`
  have hx₁ : (e x : Y) ∈ e '' interior (closure (interior A)) :=
    ⟨x, hx, rfl⟩
  -- Rewrite using `e.image_interior`
  have hx₂ : (e x : Y) ∈ interior (e '' closure (interior A)) := by
    simpa [e.image_interior (s := closure (interior A))] using hx₁
  -- Rewrite using `e.image_closure`
  have hx₃ : (e x : Y) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (s := interior A)] using hx₂
  -- Rewrite using `e.image_interior` once more
  simpa [e.image_interior (s := A)] using hx₃

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P1 B) : Topology.P1 (e ⁻¹' B) := by
  -- First, apply the image version to the inverse homeomorphism.
  have hP1 : Topology.P1 ((e.symm) '' B) :=
    Topology.P1_image_homeomorph (e := e.symm) (A := B) hB
  -- Identify this image with the desired preimage.
  have hEq : ((e.symm) '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp [Set.preimage] at *
      simpa using hy
    · intro hx
      dsimp [Set.preimage] at hx
      exact ⟨e x, hx, by
        simp⟩
  -- Conclude using the set equality.
  simpa [hEq] using hP1

theorem P3_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P3 (Set.prod A B) ↔ Topology.P3 (Set.prod B A)) := by
  -- Define the homeomorphism swapping the factors
  let e := (Homeomorph.prodComm X Y)
  -- Describe the image of `A ×ˢ B`
  have h_image_eq :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      dsimp [e, Homeomorph.prodComm, Set.prod] at hq ⊢
      rcases hq with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro hxA hyB
      · simp [e, Homeomorph.prodComm]
  -- Describe the preimage of `B ×ˢ A`
  have h_preimage_eq :
      (e ⁻¹' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · intro hp
      dsimp [Set.preimage] at hp
      dsimp [e, Homeomorph.prodComm, Set.prod] at hp
      exact And.intro hp.2 hp.1
    · intro hp
      dsimp [Set.preimage]
      dsimp [e, Homeomorph.prodComm, Set.prod]
      exact And.intro hp.2 hp.1
  -- Forward implication
  have forward :
      Topology.P3 (Set.prod A B) → Topology.P3 (Set.prod B A) := by
    intro h
    have h' : Topology.P3 (e '' Set.prod A B) :=
      Topology.P3_image_homeomorph (e := e) (A := Set.prod A B) h
    simpa [h_image_eq] using h'
  -- Backward implication
  have backward :
      Topology.P3 (Set.prod B A) → Topology.P3 (Set.prod A B) := by
    intro h
    have h' : Topology.P3 (e ⁻¹' Set.prod B A) :=
      Topology.P3_preimage_homeomorph (e := e) (B := Set.prod B A) h
    simpa [h_preimage_eq] using h'
  exact ⟨forward, backward⟩

theorem P1_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : IsClosed B) : Topology.P1 (A \ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∉ B := hx.2
  have hx_cl : x ∈ closure (interior A) := hA hxA
  -- show `x ∈ closure (interior (A \ B))`
  have : x ∈ closure (interior (A \ B)) := by
    -- use the neighbourhood formulation of being in the closure
    apply (mem_closure_iff).2
    intro V hV hxV
    -- intersect the neighbourhood with `Bᶜ`
    have hB_open : IsOpen (Bᶜ : Set X) := by
      simpa using hB.isOpen_compl
    have hW_open : IsOpen (V ∩ Bᶜ) := IsOpen.inter hV hB_open
    have hxW : x ∈ V ∩ Bᶜ := And.intro hxV hx_notB
    -- by closeness of `interior A`, this set meets it
    have h_nonempty : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
      have h_mem := (mem_closure_iff).1 hx_cl
      have h := h_mem (V ∩ Bᶜ) hW_open hxW
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using h
    rcases h_nonempty with ⟨y, ⟨⟨hyV, hy_notB⟩, hy_intA⟩⟩
    -- build an open subset of `A \ B` containing `y`
    have hy_int_diff : y ∈ interior (A \ B) := by
      have hS_open : IsOpen (interior A ∩ Bᶜ : Set X) :=
        isOpen_interior.inter hB.isOpen_compl
      have hS_sub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        rcases hz with ⟨hz_intA, hz_notB⟩
        have hzA : z ∈ A := interior_subset hz_intA
        exact And.intro hzA hz_notB
      have hS_subset_int : (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) :=
        interior_maximal hS_sub hS_open
      have hzS : y ∈ (interior A ∩ Bᶜ) := And.intro hy_intA hy_notB
      exact hS_subset_int hzS
    exact ⟨y, And.intro hyV hy_int_diff⟩
  exact this

theorem P2_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P2 (Set.prod A B) ↔ Topology.P2 (Set.prod B A)) := by
  -- Let `e` be the homeomorphism swapping the two factors
  let e := (Homeomorph.prodComm X Y)
  -- The image of `A ×ˢ B` by `e` is `B ×ˢ A`
  have h_image_eq :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      dsimp [Set.prod] at hq ⊢
      rcases hq with ⟨hxA, hyB⟩
      simpa [e] using And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro hxA hyB
      · simpa [e]
  -- The preimage of `B ×ˢ A` by `e` is `A ×ˢ B`
  have h_preimage_eq :
      (e ⁻¹' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · intro hp
      dsimp [Set.preimage] at hp
      dsimp [e] at hp
      dsimp [Set.prod] at hp ⊢
      simpa [And.comm] using hp
    · intro hp
      dsimp [Set.preimage]
      dsimp [e]
      dsimp [Set.prod] at hp ⊢
      simpa [And.comm] using hp
  -- Forward implication
  have forward :
      Topology.P2 (Set.prod A B) → Topology.P2 (Set.prod B A) := by
    intro h
    have h' : Topology.P2 (e '' Set.prod A B) :=
      Topology.P2_image_homeomorph (e := e) (A := Set.prod A B) h
    simpa [h_image_eq] using h'
  -- Backward implication
  have backward :
      Topology.P2 (Set.prod B A) → Topology.P2 (Set.prod A B) := by
    intro h
    have h' : Topology.P2 (e ⁻¹' Set.prod B A) :=
      Topology.P2_preimage_homeomorph (e := e) (B := Set.prod B A) h
    simpa [h_preimage_eq] using h'
  exact ⟨forward, backward⟩

theorem P1_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P1 (Set.prod A B) ↔ Topology.P1 (Set.prod B A)) := by
  -- Define the homeomorphism swapping the two factors
  let e := (Homeomorph.prodComm X Y)
  -- The image of `A ×ˢ B` under `e` is `B ×ˢ A`
  have h_image_eq :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      dsimp [e, Homeomorph.prodComm] at *
      dsimp [Set.prod] at hq ⊢
      rcases hq with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro hxA hyB
      · simp [e, Homeomorph.prodComm]
  -- The preimage of `B ×ˢ A` under `e` is `A ×ˢ B`
  have h_preimage_eq :
      (e ⁻¹' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · intro hp
      dsimp [Set.preimage, e, Homeomorph.prodComm, Set.prod] at hp
      exact And.intro hp.2 hp.1
    · intro hp
      dsimp [Set.preimage, e, Homeomorph.prodComm, Set.prod]
      exact And.intro hp.2 hp.1
  -- Forward implication
  have forward :
      Topology.P1 (Set.prod A B) → Topology.P1 (Set.prod B A) := by
    intro h
    have h' : Topology.P1 (e '' Set.prod A B) :=
      Topology.P1_image_homeomorph (e := e) (A := Set.prod A B) h
    simpa [h_image_eq] using h'
  -- Backward implication
  have backward :
      Topology.P1 (Set.prod B A) → Topology.P1 (Set.prod A B) := by
    intro h
    have h' : Topology.P1 (e ⁻¹' Set.prod B A) :=
      Topology.P1_preimage_homeomorph (e := e) (B := Set.prod B A) h
    simpa [h_preimage_eq] using h'
  exact ⟨forward, backward⟩

theorem P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : interior A = Set.univ) : Topology.P1 A := by
  dsimp [Topology.P1] at *
  intro x hx
  simpa [hA, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (Set.prod (Set.prod A B) C) := by
  have hAB : Topology.P1 (Set.prod A B) := Topology.P1_prod hA hB
  simpa using (Topology.P1_prod hAB hC)

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : IsClosed B) : Topology.P2 (A \ B) := by
  dsimp [Topology.P2] at *
  intro x hx
  -- Decompose the membership of `x`
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∉ B := hx.2
  -- `P2 A` gives the following interior membership
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- Define an auxiliary open neighbourhood of `x`
  let S : Set X := interior (closure (interior A)) ∩ Bᶜ
  have hS_open : IsOpen S := by
    dsimp [S]
    exact IsOpen.inter isOpen_interior hB.isOpen_compl
  have hxS : x ∈ S := by
    dsimp [S] at *
    exact And.intro hx_int hx_notB
  -- Show that `S ⊆ closure (interior (A \ B))`
  have hS_subset : (S) ⊆ closure (interior (A \ B)) := by
    intro y hy
    dsimp [S] at hy
    -- Split the conditions on `y`
    have hy_int : y ∈ interior (closure (interior A)) := hy.1
    have hy_notB : y ∉ B := hy.2
    -- From the first, we also get `y ∈ closure (interior A)`
    have hy_cl : y ∈ closure (interior A) := interior_subset hy_int
    -- Prove `y ∈ closure (interior (A \ B))`
    apply (mem_closure_iff).2
    intro V hV hyV
    -- Intersect the neighbourhood with `Bᶜ`
    have hW_open : IsOpen (V ∩ Bᶜ : Set X) :=
      IsOpen.inter hV hB.isOpen_compl
    have hyW : y ∈ V ∩ Bᶜ := And.intro hyV hy_notB
    -- Since `y ∈ closure (interior A)`, this intersection meets `interior A`
    have h_nonempty : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
      have h_mem := (mem_closure_iff).1 hy_cl
      have h := h_mem (V ∩ Bᶜ) hW_open hyW
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using h
    rcases h_nonempty with ⟨z, hz⟩
    -- Break down the membership of `z`
    have hzV : z ∈ V := (hz.1).1
    have hz_notB : z ∉ B := (hz.1).2
    have hz_intA : z ∈ interior A := hz.2
    -- Build an open subset of `A \ B` containing `z`
    have hT_open : IsOpen (interior A ∩ Bᶜ : Set X) :=
      IsOpen.inter isOpen_interior hB.isOpen_compl
    have hT_sub : (interior A ∩ Bᶜ : Set X) ⊆ (A \ B) := by
      intro w hw
      exact And.intro (interior_subset hw.1) hw.2
    have hz_interior_diff : z ∈ interior (A \ B) := by
      have hzT : z ∈ interior A ∩ Bᶜ := And.intro hz_intA hz_notB
      have := interior_maximal hT_sub hT_open
      exact this hzT
    -- Provide the desired witness in `V ∩ interior (A \ B)`
    exact ⟨z, And.intro hzV hz_interior_diff⟩
  -- Upgrade the inclusion using maximality of the interior
  have hS_subset_int : (S) ⊆ interior (closure (interior (A \ B))) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`
  have hx_final : x ∈ interior (closure (interior (A \ B))) :=
    hS_subset_int hxS
  simpa using hx_final

theorem P3_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P3 A) (hB : IsClosed B) : Topology.P3 (A \ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  -- Decompose the membership of `x`
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∉ B := hx.2
  -- `P3 A` gives an interior membership
  have hx_int : x ∈ interior (closure A) := hA hxA
  -- Define an auxiliary open neighbourhood
  let S : Set X := interior (closure A) ∩ Bᶜ
  have hS_open : IsOpen S := by
    dsimp [S]
    exact IsOpen.inter isOpen_interior hB.isOpen_compl
  have hxS : x ∈ S := by
    dsimp [S]
    exact And.intro hx_int hx_notB
  -- Show that `S ⊆ closure (A \ B)`
  have hS_subset : (S : Set X) ⊆ closure (A \ B) := by
    intro y hy
    dsimp [S] at hy
    have hy_int : y ∈ interior (closure A) := hy.1
    have hy_notB : y ∉ B := hy.2
    have hy_cl : y ∈ closure A := interior_subset hy_int
    -- Prove `y ∈ closure (A \ B)` using neighbourhoods
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hV hyV
      -- Refine the neighbourhood to avoid `B`
      have hW_open : IsOpen (V ∩ Bᶜ) := IsOpen.inter hV hB.isOpen_compl
      have hyW : y ∈ V ∩ Bᶜ := And.intro hyV hy_notB
      -- Because `y ∈ closure A`, this intersection meets `A`
      have h_nonempty : ((V ∩ Bᶜ) ∩ A).Nonempty := by
        have h_mem := (mem_closure_iff).1 hy_cl
        have h := h_mem (V ∩ Bᶜ) hW_open hyW
        simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using h
      rcases h_nonempty with ⟨z, hz⟩
      -- Extract the desired witness in `V ∩ (A \ B)`
      have hzV : z ∈ V := (hz.1).1
      have hz_notB : z ∉ B := (hz.1).2
      have hzA : z ∈ A := hz.2
      exact
        ⟨z, And.intro hzV (And.intro hzA hz_notB)⟩
    exact this
  -- Upgrade the inclusion via maximality of the interior
  have hS_subset_int : (S : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`
  exact hS_subset_int hxS

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (Set.prod (Set.prod A B) C) := by
  have hAB : Topology.P2 (Set.prod A B) := Topology.P2_prod hA hB
  simpa using Topology.P2_prod hAB hC

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (Set.prod (Set.prod A B) C) := by
  have hAB : Topology.P3 (Set.prod A B) := Topology.P3_prod hA hB
  simpa using Topology.P3_prod hAB hC

theorem P2_iff_P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 A ↔ Topology.P1 A := by
  simpa [Topology.P1_iff_P3_of_dense_interior (X := X) (A := A) h]
    using (Topology.P2_iff_P1_and_P3 (X := X) (A := A))

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro _hP2
    exact Topology.P3_of_open (A := A) hA
  · intro _hP3
    exact Topology.P2_of_open (A := A) hA

theorem P1_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 (Aᶜ) := by
  exact Topology.P1_of_open (A := Aᶜ) hA.isOpen_compl

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx_closureA
  -- Using `P1 A`, we know `closure (interior A) = closure A`.
  have h_eq := closure_eq_of_P1 hA
  -- Rewrite `hx_closureA` so that it lies in `closure (interior A)`.
  have hx_closure_intA : x ∈ closure (interior A) := by
    simpa [h_eq] using hx_closureA
  -- `interior A ⊆ interior (closure A)`
  have h_interior_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure)
  -- Taking closures preserves the inclusion.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_interior_subset
  -- Conclude.
  exact h_closure_subset hx_closure_intA

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : Topology.P1 (Set.univ : Set Y) := by
    exact Topology.P1_of_open (A := (Set.univ : Set Y)) isOpen_univ
  simpa using Topology.P1_prod hA h_univ

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : Topology.P2 (Set.univ : Set Y) := Topology.P2_univ (X := Y)
  simpa using
    (Topology.P2_prod (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 A) : Topology.P3 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : Topology.P3 (Set.univ : Set Y) := Topology.P3_univ (X := Y)
  simpa using
    (Topology.P3_prod (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P2_union₄ {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) : Topology.P2 (A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`
  have hABC : Topology.P2 (A ∪ B ∪ C) :=
    Topology.P2_union₃ hA hB hC
  -- Then add `D`
  have hABCD : Topology.P2 ((A ∪ B ∪ C) ∪ D) :=
    Topology.P2_union hABC hD
  -- Rewrite to the desired union of four sets
  simpa [Set.union_assoc] using hABCD

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : interior (closure (interior A)) = interior (closure A) := by
  -- Obtain `P1 A` from `P2 A`
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hA
  -- Hence the closures coincide
  have h_cl : closure (interior A) = closure A :=
    Topology.closure_eq_of_P1 hP1
  -- Rewrite using this equality
  simpa [h_cl]

theorem P3_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 (closure A) := by
  dsimp [Topology.P3] at *
  simpa [closure_closure] using h

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) (hD : Topology.P1 D) : Topology.P1 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  -- First, build `P1` for the triple product `A ×ˢ B ×ˢ C`.
  have hABC : Topology.P1 (Set.prod (Set.prod A B) C) :=
    Topology.P1_prod_three (A := A) (B := B) (C := C) hA hB hC
  -- Then combine it with `D`.
  simpa using
    (Topology.P1_prod (A := Set.prod (Set.prod A B) C) (B := D) hABC hD)

theorem P2_univ_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : Topology.P2 (Set.prod (Set.univ : Set X) (Set.univ : Set Y)) := by
  have hX : Topology.P2 (Set.univ : Set X) := Topology.P2_univ (X := X)
  simpa using
    (Topology.P2_prod_univ (X := X) (Y := Y) (A := (Set.univ : Set X)) hX)

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, Topology.P2 A) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h A hA_mem
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  exact h_subset hx_in

theorem P3_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P3 (A i)) : Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hP3i : Topology.P3 (A i) := h i
  have hx_in : x ∈ interior (closure (A i)) := hP3i hxAi
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact h_subset hx_in

theorem P1_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hC : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  -- Obtain `P2 A` from the closedness of `A` and the given `P3 A`
  have hP2 : Topology.P2 A :=
    ((Topology.P2_iff_P3_of_closed (A := A) hC).2 hP3)
  -- Conclude `P1 A` from `P2 A`
  exact Topology.P2_implies_P1 (A := A) hP2

theorem P3_iff_exists_open_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, ?_⟩
    · -- `A ⊆ interior (closure A)`
      dsimp [Topology.P3] at hP3
      exact hP3
    · -- `closure (interior (closure A)) = closure A`
      simpa using (closure_eq_of_P3 hP3).symm
  · rintro ⟨U, hU_open, hAU, h_cl⟩
    dsimp [Topology.P3]
    intro x hxA
    have hxU : x ∈ U := hAU hxA
    -- `U ⊆ interior (closure U)` since `U` is open and `U ⊆ closure U`
    have hU_to_interior : (U : Set X) ⊆ interior (closure U) :=
      interior_maximal (by
        intro y hy
        exact subset_closure hy) hU_open
    have hx_int_clU : x ∈ interior (closure U) := hU_to_interior hxU
    simpa [h_cl] using hx_int_clU

theorem P3_implies_P1_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h_eq : closure A = closure (interior A)) : Topology.P3 A → Topology.P1 A := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hxA
  have hx_cl : x ∈ closure A :=
    (interior_subset : interior (closure A) ⊆ closure A) (hP3 hxA)
  simpa [h_eq] using hx_cl

theorem P2_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) (hD : Topology.P2 D) (hE : Topology.P2 E) : Topology.P2 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  -- First, build `P2` for the triple product `A ×ˢ B ×ˢ C`.
  have hABC : Topology.P2 (Set.prod (Set.prod A B) C) :=
    Topology.P2_prod_three hA hB hC
  -- Next, incorporate `D`, obtaining a quadruple product.
  have hABCD : Topology.P2 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    Topology.P2_prod hABC hD
  -- Finally, add `E` to reach the quintuple product.
  simpa using Topology.P2_prod hABCD hE

theorem P1_bool_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ Topology.P1 (Aᶜᶜ) := by
  have h : (Aᶜᶜ : Set X) = A := by
    ext x
    simp
  simpa [h]

theorem P1_uniform_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → Topology.P1 (closure A) := by
  intro h_open
  exact Topology.P1_closure (A := A) (Topology.P1_of_open (A := A) h_open)

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  exact Set.empty_subset _

theorem P2_sUnion_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (⋃₀ (∅ : Set (Set X))) := by
  simpa [Set.sUnion_empty] using (Topology.P2_empty (X := X))

theorem P1_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : closure (interior (closure A)) = closure A := by
  -- First, `closure A` satisfies `P1`.
  have hP1_closure : Topology.P1 (closure A) :=
    Topology.P1_closure (A := A) h
  -- Apply the equality given by `P1` to `closure A`.
  have h_eq : closure (interior (closure A)) = closure (closure A) :=
    Topology.closure_eq_of_P1 (A := closure A) hP1_closure
  -- `closure (closure A)` simplifies to `closure A`.
  simpa [closure_closure] using h_eq

theorem P3_open_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : (Topology.P3 A ↔ interior A = A) := by
  have h_eq : interior A = A := hA.interior_eq
  exact
    ⟨fun _ => h_eq, fun _ => Topology.P3_of_open (A := A) hA⟩

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h2 : closure A = Set.univ) : Topology.P2 A := by
  -- Unfold the definitions of `P1` and `P2`
  dsimp [Topology.P1, Topology.P2] at *
  intro x hxA
  -- From `P1`, we have `A ⊆ closure (interior A)`, hence
  -- `closure A ⊆ closure (interior A)`.
  have h_closure_sub : (closure A : Set X) ⊆ closure (interior A) := by
    have hA_subset : (A : Set X) ⊆ closure (interior A) := h1
    have h := closure_mono hA_subset
    simpa [closure_closure] using h
  -- Using `closure A = univ`, deduce `closure (interior A) = univ`.
  have h_univ : (closure (interior A) : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · intro y hy; exact Set.mem_univ y
    · have : (Set.univ : Set X) ⊆ closure (interior A) := by
        simpa [h2] using h_closure_sub
      exact this
  -- Therefore every point of `A` (in particular `x`) lies in the desired interior.
  have : x ∈ interior (closure (interior A)) := by
    have hx_univ : x ∈ (Set.univ : Set X) := Set.mem_univ x
    simpa [h_univ, interior_univ] using hx_univ
  exact this

theorem P3_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 (Aᶜ) := by
  simpa using (Topology.P3_of_open (A := Aᶜ) hA.isOpen_compl)

theorem P3_iff_P1_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (closure A)) : Topology.P3 A ↔ Topology.P1 (closure A) := by
  -- The closure of `A` is open by assumption, hence its interior is itself.
  have h_int_eq : interior (closure A) = closure A := hA.interior_eq
  -- Consequently, `closure (interior (closure A)) = closure A`.
  have h_cl_eq : closure (interior (closure A)) = closure A := by
    simpa [h_int_eq, closure_closure]
  -- `P1 (closure A)` holds unconditionally under these equalities.
  have hP1_closure : Topology.P1 (closure A) := by
    dsimp [Topology.P1]
    intro x hx
    simpa [h_cl_eq] using hx
  -- Likewise, `P3 A` always holds because `A ⊆ closure A = interior (closure A)`.
  have hP3A : Topology.P3 A := by
    dsimp [Topology.P3]
    intro x hx
    have hx_cl : x ∈ closure A := subset_closure hx
    simpa [h_int_eq] using hx_cl
  exact ⟨fun _ => hP1_closure, fun _ => hP3A⟩

theorem P1_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod (interior A) (interior B)) := by
  -- We first note that the interiors of `A` and `B` satisfy `P1`.
  have hA_int : Topology.P1 (interior A) := by
    simpa using (Topology.P1_interior (A := A))
  have hB_int : Topology.P1 (interior B) := by
    simpa using (Topology.P1_interior (A := B))
  -- Apply the product theorem for `P1`.
  simpa using
    (Topology.P1_prod (A := interior A) (B := interior B) hA_int hB_int)

theorem P2_sUnion_pair {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (⋃₀ ({A, B} : Set (Set X))) := by
  -- Build the required hypothesis for every set in the pair `{A, B}`.
  have h_all : ∀ C : Set X, C ∈ ({A, B} : Set (Set X)) → Topology.P2 C := by
    intro C hC
    -- Membership in `{A, B}` means `C = A` or `C = B`.
    have h_cases : C = A ∨ C = B := by
      -- `{A, B}` is `insert A {B}`; use `mem_insert_iff`.
      have h' : C = A ∨ C ∈ ({B} : Set (Set X)) := (Set.mem_insert_iff).1 hC
      cases h' with
      | inl hEq => exact Or.inl hEq
      | inr hCB =>
          have hEqB : C = B := by
            simpa [Set.mem_singleton_iff] using hCB
          exact Or.inr hEqB
    -- Deduce `P2 C` from the corresponding hypothesis.
    cases h_cases with
    | inl hEq => simpa [hEq] using hA
    | inr hEq => simpa [hEq] using hB
  -- Apply the general `sUnion` theorem using the hypothesis we just built.
  simpa using
    (Topology.P2_sUnion (X := X) (𝒜 := ({A, B} : Set (Set X))) h_all)

theorem P1_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hAB : A ⊆ B) (hB : B ⊆ closure (interior A)) : Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` lies in `closure (interior A)` by the hypothesis `hB`.
  have hx_clA : x ∈ closure (interior A) := hB hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have h_int_sub : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have h_cl_sub : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_sub
  -- Therefore, `x` lies in `closure (interior B)`.
  exact h_cl_sub hx_clA

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∩ B) := by
  classical
  -- Unfold `P2`.
  dsimp [Topology.P2] at *
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Abbreviations.
  set U₁ : Set X := interior (closure (interior A)) with hU₁
  set U₂ : Set X := interior (closure (interior B)) with hU₂
  -- `x` belongs to both `U₁` and `U₂`.
  have hxU₁ : x ∈ U₁ := by
    simpa [hU₁] using hA hxA
  have hxU₂ : x ∈ U₂ := by
    simpa [hU₂] using hB hxB
  -- Define an open neighbourhood of `x`.
  let S : Set X := U₁ ∩ U₂
  have hS_open : IsOpen S := by
    simpa [hU₁, hU₂] using (isOpen_interior.inter isOpen_interior)
  have hxS : x ∈ S := And.intro hxU₁ hxU₂
  -- Main inclusion: `S ⊆ closure (interior (A ∩ B))`.
  have hS_subset :
      (S : Set X) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyU₁, hyU₂⟩
    -- `y` lies in the closures of the interiors of `A` and `B`.
    have hy_clA : y ∈ closure (interior A) := by
      have : y ∈ interior (closure (interior A)) := by
        simpa [hU₁] using hyU₁
      exact (interior_subset : interior (closure (interior A)) ⊆
                               closure (interior A)) this
    have hy_clB : y ∈ closure (interior B) := by
      have : y ∈ interior (closure (interior B)) := by
        simpa [hU₂] using hyU₂
      exact (interior_subset : interior (closure (interior B)) ⊆
                               closure (interior B)) this
    -- Show that every neighbourhood of `y` meets `interior (A ∩ B)`.
    refine (mem_closure_iff).2 ?_
    intro V hV hyV
    -- First step: intersect the neighbourhood with `U₂`.
    let W : Set X := V ∩ U₂
    have hW_open : IsOpen W := hV.inter (by
      simpa [hU₂] using isOpen_interior)
    have hyW : y ∈ W := ⟨hyV, hyU₂⟩
    -- `W` meets `interior A`.
    have h_nonempty₁ :
        (W ∩ interior A).Nonempty := by
      have h_cl := (mem_closure_iff).1 hy_clA
      exact h_cl W hW_open hyW
    rcases h_nonempty₁ with ⟨z, hz⟩
    -- Decompose the information on `z`.
    have hzV      : z ∈ V := hz.1.1
    have hzU₂     : z ∈ U₂ := hz.1.2
    have hz_intA  : z ∈ interior A := hz.2
    -- From `hzU₂` we obtain `z ∈ closure (interior B)`.
    have hz_clB : z ∈ closure (interior B) := by
      have : z ∈ interior (closure (interior B)) := by
        simpa [hU₂] using hzU₂
      exact (interior_subset : interior (closure (interior B)) ⊆
                               closure (interior B)) this
    -- Second step: intersect the neighbourhood with `interior A`.
    let V₂ : Set X := V ∩ interior A
    have hV₂_open : IsOpen V₂ := hV.inter isOpen_interior
    have hzV₂ : z ∈ V₂ := ⟨hzV, hz_intA⟩
    -- `V₂` meets `interior B`.
    have h_nonempty₂ : (V₂ ∩ interior B).Nonempty := by
      have h_cl := (mem_closure_iff).1 hz_clB
      exact h_cl V₂ hV₂_open hzV₂
    rcases h_nonempty₂ with ⟨w, hw⟩
    -- Extract the required memberships for `w`.
    have hwV      : w ∈ V := hw.1.1
    have hw_intA  : w ∈ interior A := hw.1.2
    have hw_intB  : w ∈ interior B := hw.2
    -- Hence `w` lies in `interior (A ∩ B)`.
    have hw_intAB : w ∈ interior (A ∩ B) := by
      -- `interior (A ∩ B) = interior A ∩ interior B`.
      have : w ∈ interior A ∩ interior B := ⟨hw_intA, hw_intB⟩
      simpa [interior_inter] using this
    -- Provide the witness required by `mem_closure_iff`.
    exact ⟨w, hwV, hw_intAB⟩
  -- Using maximality of the interior.
  have hS_subset_int :
      (S : Set X) ⊆ interior (closure (interior (A ∩ B))) :=
    interior_maximal hS_subset hS_open
  -- Conclude for the original point `x`.
  exact hS_subset_int hxS

theorem P3_of_interior_closure_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior (closure A)) = Set.univ) : Topology.P3 A := by
  -- First, show that `closure A = Set.univ`.
  have h_closure_univ : (closure A : Set X) = Set.univ := by
    -- `closure (interior (closure A)) ⊆ closure A`.
    have h_sub : closure (interior (closure A)) ⊆ closure A := by
      -- This follows from monotonicity of `closure` applied to
      -- `interior_subset : interior (closure A) ⊆ closure A`.
      simpa [closure_closure] using
        closure_mono
          (interior_subset : interior (closure A) ⊆ closure A)
    -- Rewrite the left‐hand side using the hypothesis `h`.
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [h] using h_sub
    -- Combine the two inclusions to obtain the equality.
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Consequently, `interior (closure A) = Set.univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure_univ, interior_univ]
  -- Finish the proof of `P3 A`.
  dsimp [Topology.P3]
  intro x hxA
  -- With the preceding equality, the desired membership is immediate.
  simpa [h_int_univ] using (Set.mem_univ x)

theorem P1_of_dense_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ closure (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1] at *
  exact Set.Subset.trans subset_closure h

theorem P2_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (Aᶜ) := by
  simpa using (Topology.P2_of_open (A := Aᶜ) hA.isOpen_compl)

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is open and contained in `closure (interior A)`,
  -- hence it is contained in the *interior* of that closure.
  have h_sub : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := by
      intro y hy
      exact subset_closure hy
    exact interior_maximal h_subset isOpen_interior
  -- Taking closures preserves inclusions.
  have h_closure :
      (closure (interior A) : Set X) ⊆
        closure (interior (closure (interior A))) :=
    closure_mono h_sub
  exact h_closure hx

theorem P1_univ_iff {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Topology.P1_of_open (A := (Set.univ : Set X)) isOpen_univ

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {B : Set Y} (hB : IsOpen B) : Topology.P2 (f ⁻¹' B) := by
  -- The preimage of an open set under a continuous map is open.
  have hOpen : IsOpen (f ⁻¹' B) := hB.preimage hf
  -- Open sets satisfy `P2`.
  exact Topology.P2_of_open (A := f ⁻¹' B) hOpen

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we obtain the desired inclusion
    -- between the closures.
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  · intro h
    -- Unfold the definition of `P1`.
    dsimp [Topology.P1]
    intro x hxA
    -- First send `x` into `closure A`, then use the hypothesis `h`.
    have hx_cl : (x : X) ∈ closure A := subset_closure hxA
    exact h hx_cl

theorem P2_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod (interior A) (interior B)) := by
  -- The interiors of `A` and `B` satisfy `P2`.
  have hA_int : Topology.P2 (interior A) := by
    simpa using (Topology.P2_interior (A := A))
  have hB_int : Topology.P2 (interior B) := by
    simpa using (Topology.P2_interior (A := B))
  -- Apply the product theorem for `P2`.
  simpa using
    (Topology.P2_prod (A := interior A) (B := interior B) hA_int hB_int)

theorem P2_univ_iff {X : Type*} [TopologicalSpace X] : (Topology.P2 (Set.univ : Set X)) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact Topology.P2_univ (X := X)

theorem P2_of_P1_and_P3' {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h2 : Topology.P3 A) : Topology.P2 A := by
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨h1, h2⟩

theorem P1_prod_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure (Set.prod A B)) := by
  have hAB : Topology.P1 (Set.prod A B) := Topology.P1_prod hA hB
  simpa using (Topology.P1_closure (A := Set.prod A B) hAB)

theorem P2_prod_interior_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (Set.prod (interior A) (Set.univ : Set Y)) := by
  -- The interior of `A` satisfies `P2`.
  have h_int : Topology.P2 (interior A) := by
    simpa using (Topology.P2_interior (A := A))
  -- Apply the `P2_prod_univ` theorem with `interior A`.
  simpa using
    (Topology.P2_prod_univ (X := X) (Y := Y) (A := interior A) h_int)

theorem P3_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod (interior A) (interior B)) := by
  -- The interiors of `A` and `B` satisfy `P3`.
  have hA_int : Topology.P3 (interior A) := by
    simpa using (Topology.P3_interior (A := A))
  have hB_int : Topology.P3 (interior B) := by
    simpa using (Topology.P3_interior (A := B))
  -- Apply the product theorem for `P3`.
  simpa using
    (Topology.P3_prod (A := interior A) (B := interior B) hA_int hB_int)