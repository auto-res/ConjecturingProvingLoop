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


theorem P1_of_P2 {A : Set X} (h : P2 A) : P1 A := by
  unfold P1 P2 at *
  exact subset_trans h interior_subset

theorem exists_set_with_P3 [Nonempty X] : ∃ A : Set X, P3 A := by
  exact ⟨(∅ : Set X), by
    simp [P3]⟩

theorem P1_iff_closure_interior_subset {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  unfold P1
  constructor
  · intro h
    apply subset_antisymm
    · exact closure_mono interior_subset
    ·
      have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
      simpa [closure_closure] using h'
  · intro h_eq
    have : (A : Set X) ⊆ closure A := subset_closure
    simpa [h_eq] using this

theorem interior_subset_of_P2 {A : Set X} (h : P2 A) : interior A ⊆ interior (closure (interior A)) := subset_trans interior_subset h

theorem closure_eq_of_P3 {A : Set X} (h : P3 A) : closure A = closure (interior (closure A)) := by
  apply subset_antisymm
  · exact closure_mono h
  ·
    have : interior (closure A) ⊆ closure A := interior_subset
    simpa [closure_closure] using closure_mono this

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- expand the definition of `P1`
  unfold P1 at hA hB ⊢
  -- we prove the required subset relation point-wise
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_clA : x ∈ closure (interior A) := hA hxA
      -- enlarge the set via monotonicity of `interior` and `closure`
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_sub hx_clA
  | inr hxB =>
      -- `x ∈ B`
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_sub hx_clB

theorem P2_image_homeomorph {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h : P2 A) : P2 (e '' A) := by
  classical
  -- unpack the definition of `P2`
  unfold P2 at h ⊢
  intro y hy
  -- choose a preimage of `y`
  rcases hy with ⟨x, hxA, rfl⟩
  -- apply the hypothesis on `A`
  have hx : x ∈ interior (closure (interior A)) := h hxA
  -- Step 1: transport through `e`
  have hx1 : e x ∈ interior (e '' closure (interior A)) := by
    -- first, `e x` lies in the image of the interior
    have hmem : (e x) ∈ (e '' interior (closure (interior A))) := ⟨x, hx, rfl⟩
    -- translate via `image_interior`
    have h_eq :
        (e '' interior (closure (interior A)) : Set _) =
          interior (e '' closure (interior A)) := by
      simpa using e.image_interior (s := closure (interior A))
    simpa [h_eq] using hmem
  -- Step 2: rewrite the closure with `image_closure`
  have hx2 : e x ∈ interior (closure (e '' interior A)) := by
    have h_eq :
        (e '' closure (interior A) : Set _) = closure (e '' interior A) := by
      simpa using e.image_closure (s := interior A)
    simpa [h_eq] using hx1
  -- Step 3: identify `e '' interior A` with `interior (e '' A)`
  have hx3 : e x ∈ interior (closure (interior (e '' A))) := by
    have h_eq : (e '' interior A : Set _) = interior (e '' A) := by
      simpa using e.image_interior (s := A)
    simpa [h_eq] using hx2
  -- done
  exact hx3

theorem P1_empty : P1 (∅ : Set X) := by
  unfold P1
  simp

theorem P3_univ : P3 (Set.univ : Set X) := by
  simp [P3]

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  classical
  unfold P2 at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
      -- use monotonicity `interior ⊆ interior` via `A ⊆ A ∪ B`
      have h_sub :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have h_closure_subset :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact h_int_subset
        exact h_closure_subset
      exact h_sub hx₁
  | inr hxB =>
      -- `x ∈ B`
      have hx₁ : x ∈ interior (closure (interior B)) := hB hxB
      have h_sub :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        have h_closure_subset :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          have h_int_subset : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact h_int_subset
        exact h_closure_subset
      exact h_sub hx₁

theorem exists_nontrivial_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ P1 A := by
  classical
  -- pick the whole space as our set
  rcases ‹Nonempty X› with ⟨x₀⟩
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x₀, by simp⟩
  ·
    unfold P1
    simp

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h : P1 A) : P1 (e '' A) := by
  classical
  unfold P1 at h ⊢
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the closure of the interior of `A`
  have hx : x ∈ closure (interior A) := h hxA
  -- transport this fact through the homeomorphism
  have h1 : e x ∈ closure (e '' interior A) := by
    -- first note that `e x` is in the image of the closure
    have : e x ∈ (e '' closure (interior A) : Set _) := ⟨x, hx, rfl⟩
    -- rewrite the image of the closure
    have h_eq : (e '' closure (interior A) : Set _) = closure (e '' interior A) := by
      simpa using e.image_closure (s := interior A)
    simpa [h_eq] using this
  -- identify `e '' interior A` with `interior (e '' A)`
  have h2 : e x ∈ closure (interior (e '' A)) := by
    have h_eq : (e '' interior A : Set _) = interior (e '' A) := by
      simpa using e.image_interior (s := A)
    simpa [h_eq] using h1
  exact h2

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (h : P3 A) : P3 (e '' A) := by
  classical
  unfold P3 at h ⊢
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx : x ∈ interior (closure A) := h hxA
  have hx1 : e x ∈ interior (e '' closure A) := by
    have : e x ∈ (e '' interior (closure A) : Set _) := ⟨x, hx, rfl⟩
    have h_eq : (e '' interior (closure A) : Set _) = interior (e '' closure A) := by
      simpa using e.image_interior (s := closure A)
    simpa [h_eq] using this
  have h_eq : (e '' closure A : Set _) = closure (e '' A) := by
    simpa using e.image_closure (s := A)
  simpa [h_eq] using hx1

theorem P3_of_P2 {A : Set X} (h : P2 A) : P3 A := by
  -- unfold the definitions of `P2` and `P3`
  unfold P2 at h
  unfold P3
  -- combine the two inclusions
  exact subset_trans h (interior_mono (closure_mono interior_subset))

theorem P3_union {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  classical
  unfold P3 at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx1 : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_subset hx1
  | inr hxB =>
      have hx1 : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        have : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_subset hx1

theorem P2_interior (A : Set X) : P2 (interior A) := by
  unfold P2
  simpa [interior_interior] using
    (interior_maximal (subset_closure) isOpen_interior :
      (interior A : Set X) ⊆ interior (closure (interior A)))

theorem exists_nonempty_P3 [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ P3 A := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x₀, by simp⟩
  · simpa using (P3_univ : P3 (Set.univ : Set X))

theorem P2_iff_P1_and_P3 {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro h
    exact ⟨P1_of_P2 h, P3_of_P2 h⟩
  · rintro ⟨hP1, hP3⟩
    have h_cl : closure (interior A) = closure A :=
      (P1_iff_closure_interior_subset).1 hP1
    simpa [P2, h_cl] using hP3

theorem P3_of_dense {A : Set X} (hA : Dense A) : P3 A := by
  unfold P3
  simpa [hA.closure_eq, interior_univ] using
    (Set.subset_univ (A : Set X))

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 (X:=X) A) (h3 : P3 (X:=X) A) : P2 A := by
  -- Obtain equality of closures from `P1`
  have h_cl : closure A = closure (interior A) :=
    ((P1_iff_closure_interior_subset).1 h1).symm
  -- Unfold `P2` and prove the required inclusion
  unfold P2
  intro x hx
  -- Apply `P3` and rewrite using the closure equality
  have hx' : x ∈ interior (closure A) := h3 hx
  simpa [h_cl] using hx'

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 (X:=X) A := by
  -- Unfold the definition of `P2`
  unfold P2
  intro x hx
  -- An open set is contained in the interior of its closure
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have hx' : x ∈ interior (closure A) := h_subset hx
  -- Since `interior A = A`, rewrite the goal accordingly
  simpa [hA.interior_eq] using hx'

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 (X:=X) A := by
  -- Unfold the definition of `P3`
  unfold P3
  -- We must show `A ⊆ interior (closure A)`
  intro x hx
  -- Since `A` is open, `interior A = A`
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  -- From `A ⊆ closure A`, deduce `interior A ⊆ interior (closure A)`
  have h_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_subset hx_int

theorem exists_dense_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Dense A ∧ P2 (X := X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using dense_univ
  · simpa using P2_of_open (X := X) (A := Set.univ) isOpen_univ

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 (X := X) A := by
  classical
  unfold P2
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq, interior_univ] using this

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 (X := X) A := by
  unfold P1
  simpa [hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (X:=X) (interior A) := by
  exact
    P3_of_P2 (X := X) (A := interior A) (P2_interior (X := X) (A := A))

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 (X:=X) A) : closure (interior A) = closure (interior (closure A)) := by
  -- Obtain `P1` and `P3` from the given `P2`
  have hP1 : P1 (X := X) A := P1_of_P2 (A := A) h
  have hP3 : P3 (X := X) A := P3_of_P2 (A := A) h
  -- Translate these properties into equalities of closures
  have h1 : closure (interior A) = closure A :=
    (P1_iff_closure_interior_subset (A := A)).1 hP1
  have h2 : closure A = closure (interior (closure A)) :=
    closure_eq_of_P3 (A := A) hP3
  -- Chain the equalities
  simpa using h1.trans h2

theorem exists_dense_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Dense A ∧ P3 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using dense_univ
  · simpa using (P3_univ (X := X))

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (X:=X) (Set.univ : Set X) := by
  unfold Topology.P1
  simpa [interior_univ, closure_univ]

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (X:=X) (∅ : Set X) := by
  unfold Topology.P2
  intro x hx
  cases hx

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (X:=X) (interior A) := by
  unfold Topology.P1
  simpa using (subset_closure : (interior A : Set X) ⊆ closure (interior A))

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, Topology.P3 (X:=X) A) : Topology.P3 (X:=X) (⋃₀ 𝒜) := by
  classical
  -- Unfold the definition of `P3`
  unfold Topology.P3 at hA ⊢
  -- Take a point in the sUnion
  intro x hx
  -- Obtain the witness set `A`
  rcases hx with ⟨A, hA_mem, hxA⟩
  -- Use `P3` for this particular `A`
  have hx_int_clA : x ∈ interior (closure A) := hA A hA_mem hxA
  -- Show the needed inclusion of closures
  have h_subset : closure A ⊆ closure (⋃₀ 𝒜) := by
    apply closure_mono
    intro y hy
    exact ⟨A, hA_mem, hy⟩
  -- Monotonicity of `interior` yields the claim
  exact (interior_mono h_subset) hx_int_clA

theorem P2_Union {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P2 (X:=X) (A i)) : Topology.P2 (X:=X) (⋃ i, A i) := by
  classical
  -- unpack the definition of `P2`
  unfold Topology.P2 at h ⊢
  intro x hx
  -- choose an index witnessing `x ∈ ⋃ i, A i`
  rcases (Set.mem_iUnion).1 hx with ⟨i, hxAi⟩
  -- apply `P2` for this particular index
  have hi := h i
  -- `hi : A i ⊆ interior (closure (interior (A i)))`
  have hx₁ : x ∈ interior (closure (interior (A i))) := hi hxAi
  -- show the required inclusion of interiors
  have h_subset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    -- rely on monotonicity of `interior` and `closure`
    apply interior_mono
    have h_closure_subset :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      apply closure_mono
      have h_int_subset :
          interior (A i) ⊆ interior (⋃ j, A j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion_of_mem i hy
      exact h_int_subset
    exact h_closure_subset
  -- conclude
  exact h_subset hx₁

theorem P3_Union {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P3 (X:=X) (A i)) : Topology.P3 (X:=X) (⋃ i, A i) := by
  classical
  -- unpack the definition of `P3`
  unfold Topology.P3 at h ⊢
  intro x hx
  -- pick an index `i` such that `x ∈ A i`
  rcases (Set.mem_iUnion).1 hx with ⟨i, hxAi⟩
  -- use `P3` for this particular `i`
  have hx₁ : x ∈ interior (closure (A i)) := h i hxAi
  -- show the required inclusion of interiors
  have h_subset :
      interior (closure (A i)) ⊆
        interior (closure (⋃ j, A j)) := by
    -- rely on monotonicity of `interior` and `closure`
    apply interior_mono
    have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    exact h_closure_subset
  -- conclude
  exact h_subset hx₁

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (⋃₀ 𝒜) := by
  classical
  -- Unfold the definition of `P1`
  unfold Topology.P1 at hA ⊢
  -- Take an element of the sUnion
  intro x hx
  -- Obtain a witness set `A`
  rcases hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P1` for this particular `A`
  have hx_cl_intA : x ∈ closure (interior A) := hA A hA_mem hxA
  -- Show the needed inclusion of closures
  have h_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    apply closure_mono
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      apply interior_mono
      intro y hy
      exact ⟨A, hA_mem, hy⟩
    exact h_int_subset
  -- Conclude
  exact h_subset hx_cl_intA

theorem P3_of_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : Topology.P3 (X:=X) A := by
  intro x hx
  simpa [hA, interior_univ] using (Set.mem_univ x)

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P2 (X:=Y) B) : Topology.P2 (X:=X) (e ⁻¹' B) := by
  classical
  -- Step 1: transport `P2` through the inverse homeomorphism
  have hP2_image : Topology.P2 (X := X) (e.symm '' B) := by
    simpa using
      (Topology.P2_image_homeomorph (X := Y) (e := e.symm) (A := B) hB)
  -- Step 2: identify the image with the preimage
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp [e.symm_apply_apply]⟩
  -- Step 3: rewrite and finish
  simpa [h_eq] using hP2_image

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (hA : ∀ A ∈ 𝒜, Topology.P2 (X:=X) A) : Topology.P2 (X:=X) (⋃₀ 𝒜) := by
  classical
  -- Unpack the definition of `P2`
  unfold Topology.P2 at hA ⊢
  intro x hx
  -- Obtain a witness set `A`
  rcases hx with ⟨A, hA_mem, hxA⟩
  -- Apply `P2` for this particular `A`
  have hx₁ : x ∈ interior (closure (interior A)) := (hA A hA_mem) hxA
  -- Show the required inclusion of interiors
  have h_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) := by
    -- Use monotonicity of `interior` and `closure`
    apply interior_mono
    have h_closure_subset :
        closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
      apply closure_mono
      have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
        apply interior_mono
        intro y hy
        exact ⟨A, hA_mem, hy⟩
      exact h_int_subset
    exact h_closure_subset
  -- Conclude
  exact h_subset hx₁

theorem dense_of_P1_and_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) (h_dense : Dense (interior A)) : Dense A := by
  -- Step 1: show `closure A ⊆ closure (interior A)`
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    -- `P1` gives `A ⊆ closure (interior A)`
    -- Taking closures and simplifying yields the claim
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono h
    simpa [closure_closure] using this
  -- Step 2: the reverse inclusion `closure (interior A) ⊆ closure A`
  have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Step 3: deduce equality of the two closures
  have h_closure_eq : closure (A : Set X) = closure (interior A) :=
    (subset_antisymm h₁ h₂)
  -- Step 4: use density of `interior A`
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := by
    simpa [h_closure_eq] using h_dense.closure_eq
  -- Step 5: conclude that `A` is dense
  exact (dense_iff_closure_eq).mpr h_closure_univ

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : Topology.P3 (X:=X) A := by
  unfold Topology.P3
  -- Since `closure A` is open, its interior is itself
  have h_eq : interior (closure (A : Set X)) = closure A := by
    simpa using h_open.interior_eq
  -- The set `A` is contained in its closure
  have h_sub : (A : Set X) ⊆ closure A := subset_closure
  -- Combine the two facts
  simpa [h_eq] using h_sub

theorem P2_bUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Set ι} {A : ι → Set X} (hA : ∀ i, i ∈ s → Topology.P2 (X:=X) (A i)) : Topology.P2 (X:=X) (⋃ i, ⋃ (_h : i ∈ s), A i) := by
  classical
  -- Step 1: obtain `P2` for every index contained in `s`
  have h_subtype : ∀ z : {i // i ∈ s}, Topology.P2 (X := X) (A z.1) := by
    intro z
    exact hA z.1 z.2
  -- Step 2: apply `P2_Union` to this family
  have hP2_sub :
      Topology.P2 (X := X) (⋃ z : {i // i ∈ s}, A z.1) := by
    simpa using
      (Topology.P2_Union (X := X) (A := fun z : {i // i ∈ s} => A z.1)
        (by
          intro z
          exact h_subtype z))
  -- Step 3: identify the two unions
  have h_eq :
      (⋃ z : {i // i ∈ s}, A z.1) = ⋃ i, ⋃ _h : i ∈ s, A i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨z, hxz⟩
      rcases z with ⟨i, hi⟩
      exact
        (Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, by simpa using hxz⟩⟩)
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx₁⟩
      rcases Set.mem_iUnion.1 hx₁ with ⟨hi, hxi⟩
      exact
        (Set.mem_iUnion.2
            ⟨⟨i, hi⟩, by simpa using hxi⟩)
  -- Step 4: rewrite and conclude
  simpa [h_eq] using hP2_sub

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 (X:=X) A) (hDense : Dense A) : Topology.P2 (X:=X) A := by
  -- Unfold the definition of `P2`
  unfold Topology.P2
  intro x hx
  -- Step 1: from `P1` obtain `closure A ⊆ closure (interior A)`
  have h_closure_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
    -- `P1` gives `A ⊆ closure (interior A)`; take closures and simplify
    have h' : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono h1
    simpa [closure_closure] using h'
  -- Step 2: since `A` is dense, `closure A = univ`
  have h_univ_subset : (Set.univ : Set X) ⊆ closure (interior A) := by
    simpa [hDense.closure_eq] using h_closure_subset
  -- Step 3: deduce `closure (interior A) = univ`
  have h_cl_eq_univ : closure (interior A) = (Set.univ : Set X) := by
    apply subset_antisymm
    · exact Set.subset_univ _
    · exact h_univ_subset
  -- Step 4: hence `interior (closure (interior A)) = univ`
  have h_int_eq_univ : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_cl_eq_univ, interior_univ]
  -- Step 5: conclude the desired membership
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int_eq_univ] using this

theorem closure_eq_self_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 (X:=X) A) : closure A = closure (interior A) := by
  -- Obtain `P1` from the given `P2`
  have hP1 : Topology.P1 (X := X) A := Topology.P1_of_P2 (A := A) h
  -- Turn `P1` into the required equality
  simpa using ((Topology.P1_iff_closure_interior_subset (A := A)).1 hP1).symm

theorem exists_dense_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Dense A ∧ Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using dense_univ
  · simpa using (Topology.P1_univ (X := X))

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  constructor
  · intro _; exact P3_of_open (X := X) (A := A) hA
  · intro _; exact P1_of_open (X := X) (A := A) hA

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (h : Topology.P1 (X:=Y) B) : Topology.P1 (X:=X) (e ⁻¹' B) := by
  classical
  -- Step 1: transport `P1` through the inverse homeomorphism
  have hP1_image : Topology.P1 (X := X) (e.symm '' B) := by
    simpa using
      (Topology.P1_image_homeomorph (X := Y) (Y := X) (e := e.symm) (A := B) h)
  -- Step 2: identify the image with the preimage
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp [e.symm_apply_apply]⟩
  -- Step 3: rewrite and conclude
  simpa [h_eq] using hP1_image

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (h : Topology.P3 (X:=Y) B) : Topology.P3 (X:=X) (e ⁻¹' B) := by
  classical
  -- Step 1: transport `P3` through the inverse homeomorphism
  have hP3_image : Topology.P3 (X := X) (e.symm '' B) := by
    simpa using
      (Topology.P3_image_homeomorph (X := Y) (Y := X) (e := e.symm) (A := B) h)
  -- Step 2: identify the image with the preimage
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp [e.symm_apply_apply]⟩
  -- Step 3: rewrite and conclude
  simpa [h_eq] using hP3_image

theorem P1_union_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (A ∪ interior A) := by
  simpa using
    P1_union (A := A) (B := interior A) hA (P1_interior (A := A))

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, Topology.P1 (X:=X) (A i)) : Topology.P1 (X:=X) (⋃ i, A i) := by
  classical
  -- Unpack the definition of `P1`
  unfold Topology.P1 at h ⊢
  intro x hx
  -- Choose an index `i` with `x ∈ A i`
  rcases (Set.mem_iUnion).1 hx with ⟨i, hxAi⟩
  -- Apply `P1` for this particular `i`
  have hx₁ : x ∈ closure (interior (A i)) := h i hxAi
  -- Show the required inclusion of closures
  have h_subset :
      closure (interior (A i)) ⊆
        closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have h_int_subset :
        interior (A i) ⊆ interior (⋃ j, A j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    exact h_int_subset
  -- Conclude
  exact h_subset hx₁

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (X:=X) (Set.univ : Set X) := by
  unfold Topology.P2
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (X:=X) (∅ : Set X) := by
  unfold Topology.P3
  intro x hx
  cases hx

theorem closure_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) : closure A ⊆ closure (interior A) := by
  simpa using closure_mono h

theorem exists_compact_P2 {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ A : Set X, IsCompact A ∧ Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using isCompact_univ
  · simpa using (P2_univ (X := X))

theorem P3_bUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {s : Set ι} {A : ι → Set X} (hA : ∀ i, i ∈ s → Topology.P3 (X:=X) (A i)) : Topology.P3 (X:=X) (⋃ i, ⋃ (_ : i ∈ s), A i) := by
  classical
  -- Step 1: obtain `P3` for every index contained in `s`
  have h_subtype : ∀ z : {i // i ∈ s}, Topology.P3 (X := X) (A z.1) := by
    intro z
    exact hA z.1 z.2
  -- Step 2: apply `P3_Union` to this family
  have hP3_sub :
      Topology.P3 (X := X) (⋃ z : {i // i ∈ s}, A z.1) := by
    simpa using
      (Topology.P3_Union (X := X)
          (A := fun z : {i // i ∈ s} => A z.1) h_subtype)
  -- Step 3: identify the two unions
  have h_eq :
      (⋃ z : {i // i ∈ s}, A z.1) = ⋃ i, ⋃ (_ : i ∈ s), A i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨z, hxz⟩
      rcases z with ⟨i, hi⟩
      exact
        (Set.mem_iUnion.2
          ⟨i, Set.mem_iUnion.2 ⟨hi, by simpa using hxz⟩⟩)
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx₁⟩
      rcases Set.mem_iUnion.1 hx₁ with ⟨hi, hxi⟩
      exact
        (Set.mem_iUnion.2
          ⟨⟨i, hi⟩, by simpa using hxi⟩)
  -- Step 4: rewrite and conclude
  simpa [h_eq] using hP3_sub

theorem P2_mk_mem {X : Type*} [TopologicalSpace X] (x : X) : ∃ A : Set X, x ∈ A ∧ Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simp
  · simpa using P2_univ (X := X)

theorem exists_compact_P1 {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ A : Set X, IsCompact A ∧ Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using isCompact_univ
  · simpa using (Topology.P1_univ (X := X))

theorem exists_disjoint_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A B : Set X, A ∩ B = ∅ ∧ Topology.P1 (X:=X) A ∧ Topology.P1 (X:=X) B := by
  refine ⟨(∅ : Set X), (Set.univ : Set X), ?_, ?_, ?_⟩
  · simp
  · simpa using (P1_empty (X := X))
  · simpa using (P1_univ (X := X))

theorem P3_iff_P2_of_closed {A : Set X} (hA : IsClosed A) : P3 A ↔ P2 A := by
  constructor
  · intro hP3
    -- prove `P2 A` assuming `P3 A`
    unfold P2
    intro x hxA
    -- from `P3` we obtain membership in `interior (closure A)`
    have hx_int_cl : x ∈ interior (closure A) := hP3 hxA
    -- since `A` is closed, `closure A = A`
    have hx_intA : x ∈ interior A := by
      simpa [hA.closure_eq] using hx_int_cl
    -- `interior A ⊆ interior (closure (interior A))`
    have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      -- `interior A ⊆ closure (interior A)`
      have h_sub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      -- apply `interior_mono` and simplify
      simpa [interior_interior] using interior_mono h_sub
    exact h_subset hx_intA
  · intro hP2
    exact P3_of_P2 hP2

theorem P2_iff_P1_of_dense_interior {A : Set X} (h : Dense (interior A)) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P1_of_P2 (A := A) hP2
  · intro _hP1
    exact P2_of_dense_interior (X := X) (A := A) h

theorem P1_inter_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (A ∩ closure A) := by
  -- Unpack the definition of `P1`
  unfold Topology.P1 at h ⊢
  -- Since `A ⊆ closure A`, we have `A ∩ closure A = A`
  have h_eq : (A ∩ closure A : Set X) = A := by
    simpa using
      (Set.inter_eq_left.2 (subset_closure : (A : Set X) ⊆ closure A))
  -- Rewriting with this equality reduces the goal to the hypothesis
  simpa [h_eq] using h

theorem exists_closed_P2_of_compact {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ A : Set X, IsClosed A ∧ Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_⟩
  simpa using (Topology.P2_univ (X := X))

theorem closure_eq_inter_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 (X:=X) A) : closure A = closure (interior (closure A)) := by
  have hP3 : P3 A := P3_of_P2 (A := A) hA
  simpa using closure_eq_of_P3 (A := A) hP3

theorem P3_closed_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hd : Dense (interior A)) (hc : IsClosed A) : Topology.P3 (X:=X) A := by
  -- Step 1: show that `A = univ`
  have hA_eq_univ : (A : Set X) = Set.univ := by
    -- `closure (interior A)` is `univ` by density
    have h_cl_int_eq_univ : closure (interior A) = (Set.univ : Set X) :=
      hd.closure_eq
    -- since `A` is closed we have `closure (interior A) ⊆ A`
    have h_subset : closure (interior A) ⊆ (A : Set X) := by
      have : closure (interior A) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hc.closure_eq] using this
    -- hence `univ ⊆ A`
    have h_univ_subset : (Set.univ : Set X) ⊆ (A : Set X) := by
      simpa [h_cl_int_eq_univ] using h_subset
    -- conclude equality
    exact Set.Subset.antisymm (Set.subset_univ _) h_univ_subset
  -- Step 2: rewrite and conclude `P3 A`
  unfold Topology.P3
  simpa [hA_eq_univ, hc.closure_eq, interior_univ]

theorem P1_mul_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 (X:=X) A := by
  -- Unfold the definition of `P1`
  unfold Topology.P1
  intro x hxA
  -- In a subsingleton type, any non-empty set is the whole space
  have hAU : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hxA
  -- Rewriting with this equality solves the goal
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hAU, interior_univ, closure_univ] using this

theorem P1_iff_P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen (closure A)) : (Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A) := by
  -- `P3 A` holds automatically since the closure of `A` is open
  have hP3 : Topology.P3 (X := X) A :=
    P3_of_open_closure (X := X) (A := A) h_open
  constructor
  · intro hP1
    exact P2_of_P1_and_P3 (X := X) (A := A) hP1 hP3
  · intro hP2
    exact P1_of_P2 (A := A) hP2

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  constructor
  · intro _hP3
    exact P2_of_open (X := X) (A := A) hA
  · intro hP2
    exact P3_of_P2 (A := A) hP2

theorem exists_set_with_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Topology.P2 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_⟩
  simpa using (P2_univ (X := X))

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 (X:=X) A := by
  classical
  -- Unfold the definition of `P2`
  unfold Topology.P2
  intro x hxA
  -- Split on whether `A` is empty or not
  by_cases hA : (A : Set X).Nonempty
  · rcases hA with ⟨a, ha⟩
    -- In a subsingleton, any non-empty set is the whole space
    have hAU : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _
        have h_eq : y = a := Subsingleton.elim y a
        simpa [h_eq] using ha
    -- The target set is `univ`, so the claim is immediate
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hAU, interior_univ, closure_univ] using this
  · -- If `A` is empty, `x ∈ A` is impossible
    have hContr : (A : Set X).Nonempty := ⟨x, hxA⟩
    exact (hA hContr).elim

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 (X:=X) A := by
  classical
  unfold Topology.P3
  intro x hxA
  by_cases hA : (A : Set X).Nonempty
  · rcases hA with ⟨a, ha⟩
    have hAU : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; trivial
      · intro _; 
        have : y = a := Subsingleton.elim y a
        simpa [this] using ha
    have : x ∈ (Set.univ : Set X) := by simp
    simpa [hAU, closure_univ, interior_univ] using this
  · cases hA ⟨x, hxA⟩

theorem exists_closed_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, IsClosed A ∧ Topology.P3 (X:=X) A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_⟩
  simpa using (Topology.P3_univ (X := X))

theorem P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hd : Dense A) : Topology.P1 (X:=X) A := by
  -- `A` is both closed and dense, hence it is the whole space
  have hAU : (A : Set X) = (Set.univ : Set X) := by
    simpa [hA.closure_eq] using hd.closure_eq
  -- Unfold the definition of `P1` and solve by `simp`
  unfold Topology.P1
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hAU, interior_univ, closure_univ] using this

theorem P3_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 (X:=X) (Aᶜ) := by
  simpa using
    P3_of_open (X := X) (A := Aᶜ) ((isOpen_compl_iff).2 hA)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 (X:=X) A) (hB : Topology.P1 (X:=Y) B) : Topology.P1 (X:=X×Y) (A ×ˢ B) := by
  -- Unfold the definition of `P1`
  unfold Topology.P1 at hA hB ⊢
  -- We prove the required inclusion point-wise
  intro z hz
  -- Extract the component memberships
  have hxA : z.1 ∈ A := hz.1
  have hyB : z.2 ∈ B := hz.2
  -- Apply `P1` for each coordinate
  have hx_cl : z.1 ∈ closure (interior A) := hA hxA
  have hy_cl : z.2 ∈ closure (interior B) := hB hyB
  -- Step 1: `(z.1, z.2)` lies in the closure of `interior A ×ˢ interior B`
  have h_mem_prod : z ∈ closure (interior A ×ˢ interior B) := by
    -- Use `closure_prod_eq`
    have : z ∈ (closure (interior A) ×ˢ closure (interior B)) := ⟨hx_cl, hy_cl⟩
    simpa [closure_prod_eq] using this
  -- Step 2: `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`
  have h_subset_int :
      (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
    -- First, it is contained in `A ×ˢ B`
    have h_subset_AB :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ (A ×ˢ B) := by
      intro p hp
      exact ⟨
        (interior_subset : interior A ⊆ A) hp.1,
        (interior_subset : interior B ⊆ B) hp.2⟩
    -- Next, it is open
    have h_open :
        IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior : IsOpen (interior A)).prod
        (isOpen_interior : IsOpen (interior B))
    -- Conclude by `interior_maximal`
    exact interior_maximal h_subset_AB h_open
  -- Step 3: take closures to obtain the desired inclusion
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) := closure_mono h_subset_int
  -- Step 4: finish
  exact h_closure_subset h_mem_prod

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 (X:=X) A) (hB : Topology.P2 (X:=Y) B) : Topology.P2 (X:=X×Y) (A ×ˢ B) := by
  classical
  -- Unpack the definition of `P2`
  unfold Topology.P2 at hA hB ⊢
  intro z hz
  -- Apply `P2` to each coordinate
  have hx : z.1 ∈ interior (closure (interior A)) := hA hz.1
  have hy : z.2 ∈ interior (closure (interior B)) := hB hz.2
  -- Auxiliary open neighbourhoods in each factor
  let U : Set X := interior (closure (interior A))
  let V : Set Y := interior (closure (interior B))
  -- Openness of the auxiliary sets
  have hU_open : IsOpen U := by
    simpa [U] using
      (isOpen_interior : IsOpen (interior (closure (interior A))))
  have hV_open : IsOpen V := by
    simpa [V] using
      (isOpen_interior : IsOpen (interior (closure (interior B))))
  -- The point `z` belongs to `U ×ˢ V`
  have hzU : z.1 ∈ U := by
    simpa [U] using hx
  have hzV : z.2 ∈ V := by
    simpa [V] using hy
  have h_mem_UV : z ∈ (U ×ˢ V : Set (X × Y)) := by
    exact ⟨hzU, hzV⟩
  -- `U ×ˢ V` is open
  have hUV_open : IsOpen (U ×ˢ V : Set (X × Y)) := hU_open.prod hV_open
  -- `U ×ˢ V ⊆ closure (interior A ×ˢ interior B)`
  have hU_subset : (U : Set X) ⊆ closure (interior A) := by
    intro x hxU
    -- `interior_subset` furnishes the inclusion
    have : x ∈ interior (closure (interior A)) := by
      simpa [U] using hxU
    exact interior_subset this
  have hV_subset : (V : Set Y) ⊆ closure (interior B) := by
    intro y hyV
    have : y ∈ interior (closure (interior B)) := by
      simpa [V] using hyV
    exact interior_subset this
  have h_subset_prod :
      (U ×ˢ V : Set (X × Y)) ⊆
        (closure (interior A) ×ˢ closure (interior B)) :=
    Set.prod_mono hU_subset hV_subset
  have h_subset :
      (U ×ˢ V : Set (X × Y)) ⊆
        closure (interior A ×ˢ interior B) := by
    simpa [closure_prod_eq] using h_subset_prod
  -- Hence `z` is in the interior of that closure
  have hz_small :
      z ∈ interior (closure (interior A ×ˢ interior B)) :=
    (mem_interior.2 ⟨U ×ˢ V, h_subset, hUV_open, h_mem_UV⟩)
  -- Relate `interior A ×ˢ interior B` with `interior (A ×ˢ B)`
  have h_int_subset :
      (interior A ×ˢ interior B : Set (X × Y)) ⊆ interior (A ×ˢ B) := by
    -- First, it is contained in `A ×ˢ B`
    have h_into_AB :
        (interior A ×ˢ interior B : Set (X × Y)) ⊆ (A ×ˢ B) := by
      intro p hp
      exact
        ⟨(interior_subset : interior A ⊆ A) hp.1,
         (interior_subset : interior B ⊆ B) hp.2⟩
    -- Openness of the left-hand side
    have h_open :
        IsOpen (interior A ×ˢ interior B) :=
      (isOpen_interior : IsOpen (interior A)).prod
        (isOpen_interior : IsOpen (interior B))
    -- Use `interior_maximal`
    exact interior_maximal h_into_AB h_open
  -- Passage to closures and interiors
  have h_closure_subset :
      closure (interior A ×ˢ interior B) ⊆
        closure (interior (A ×ˢ B)) :=
    closure_mono h_int_subset
  -- Conclude via monotonicity of `interior`
  exact (interior_mono h_closure_subset) hz_small

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 (X:=X) A) (hB : Topology.P3 (X:=Y) B) : Topology.P3 (X:=X×Y) (A ×ˢ B) := by
  classical
  -- unpack the definition of `P3`
  unfold Topology.P3 at hA hB ⊢
  -- take a point in the product set
  intro z hz
  -- coordinates belong to the factors
  have hxA : z.1 ∈ A := hz.1
  have hyB : z.2 ∈ B := hz.2
  -- apply `P3` for each coordinate
  have hxU : z.1 ∈ interior (closure A) := hA hxA
  have hyV : z.2 ∈ interior (closure B) := hB hyB
  -- auxiliary open neighbourhoods
  let U : Set X := interior (closure A)
  let V : Set Y := interior (closure B)
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_interior : IsOpen (interior (closure A)))
  have hV_open : IsOpen V := by
    simpa [V] using (isOpen_interior : IsOpen (interior (closure B)))
  -- the point lies in `U ×ˢ V`
  have hzUV : z ∈ (U ×ˢ V : Set (X × Y)) := by
    exact ⟨by simpa [U] using hxU, by simpa [V] using hyV⟩
  -- `U ×ˢ V` is contained in the desired closure
  have h_subset : (U ×ˢ V : Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    -- first, `U ⊆ closure A` and `V ⊆ closure B`
    have h1 : (U : Set X) ⊆ closure A := by
      intro x hx
      have : x ∈ interior (closure A) := by simpa [U] using hx
      exact interior_subset this
    have h2 : (V : Set Y) ⊆ closure B := by
      intro y hy
      have : y ∈ interior (closure B) := by simpa [V] using hy
      exact interior_subset this
    -- combine the two inclusions
    have h_prod : (U ×ˢ V : Set (X × Y)) ⊆ (closure A ×ˢ closure B) :=
      Set.prod_mono h1 h2
    simpa [closure_prod_eq] using h_prod
  -- conclude that `z` is in the interior of the closure
  exact
    (mem_interior.2
      ⟨U ×ˢ V, h_subset, hU_open.prod hV_open, hzUV⟩)

theorem exists_set_with_all_P [Nonempty X] : ∃ A : Set X, P1 A ∧ P2 A ∧ P3 A := by
  -- Obtain a set satisfying `P2`
  rcases exists_set_with_P2 (X := X) with ⟨A, hP2⟩
  exact ⟨A, P1_of_P2 hP2, hP2, P3_of_P2 hP2⟩

theorem P2_implies_P1_or_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (X:=X) A → (Topology.P1 (X:=X) A ∨ Topology.P3 (X:=X) A) := by
  intro h
  exact Or.inl (Topology.P1_of_P2 (A := A) h)

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 (X:=X) A) : Topology.P2 (X:=X×Y) (A ×ˢ (Set.univ : Set Y)) := by
  -- `univ` satisfies `P2`, so we can apply the general `P2_prod` theorem
  have hB : Topology.P2 (X := Y) (Set.univ : Set Y) := by
    simpa using (P2_univ (X := Y))
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) hA hB)

theorem P1_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (X:=X) (closure (interior (closure (interior A)))) := by
  -- Unfold the definition of `P1`
  unfold Topology.P1
  intro x hx
  -- Let `S := interior (closure (interior A))`; we will show
  -- `closure S ⊆ closure (interior (closure S))`
  have h_subset :
      (closure (interior (closure (interior A))) : Set X) ⊆
        closure (interior (closure (interior (closure (interior A))))) := by
    -- First, prove `interior S ⊆ interior (closure S)`
    have h_int :
        (interior (closure (interior A)) : Set X) ⊆
          interior (closure (interior (closure (interior A)))) := by
      -- `interior (closure (interior A))` is open and contained in its closure
      simpa using
        (interior_maximal
            (subset_closure :
              (interior (closure (interior A)) : Set X) ⊆
                closure (interior (closure (interior A))))
            (isOpen_interior :
              IsOpen (interior (closure (interior A)))))
    -- Taking closures yields the desired inclusion
    exact closure_mono h_int
  -- Finish by applying the inclusion to the given point
  exact h_subset hx

theorem exists_finite_P1 {X : Type*} [TopologicalSpace X] [Finite X] : ∃ A : Set X, Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), ?_⟩
  simpa using (Topology.P1_univ (X := X))

theorem P1_of_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hEq : closure A = interior A) : Topology.P1 (X:=X) A := by
  unfold Topology.P1
  intro x hx
  -- `x` is in the closure of `A`
  have hx_cl : (x : X) ∈ closure A := subset_closure hx
  -- Relate the two closures using the given equality
  have h_cl_eq : closure (interior (A : Set X)) = closure A := by
    calc
      closure (interior (A : Set X))
          = closure (closure A) := by
            simpa [hEq]
      _ = closure A := by
        simpa [closure_closure]
  -- Rewrite and conclude
  simpa [h_cl_eq] using hx_cl

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 (X:=X) A) : Topology.P1 (X:=X) (closure A) := by
  -- Unfold the definition of `P1`
  unfold Topology.P1 at h ⊢
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`
  have h₁ : (closure (A : Set X)) ⊆ closure (interior A) := by
    -- take closures on both sides of `h`
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono h
    simpa [closure_closure] using this
  have hx₁ : x ∈ closure (interior A) := h₁ hx
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    have : (interior A : Set X) ⊆ interior (closure A) := by
      apply interior_mono
      exact subset_closure
    exact this
  -- Combine the two inclusions
  exact h₂ hx₁

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 (X:=X) A) : Topology.P1 (X:=X×Y) (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P1_prod (A := A) (B := (Set.univ : Set Y)) hA (P1_univ (X := Y)))

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 (X:=X) A) : Topology.P3 (X:=X×Y) (A ×ˢ (Set.univ : Set Y)) := by
  simpa using
    (P3_prod (A := A) (B := (Set.univ : Set Y)) hA (P3_univ (X := Y)))

theorem P1_closed_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (X:=X) A) (hA_closed : IsClosed A) : Topology.P1 (X:=X) (A ∩ interior A) := by
  -- Since `interior A ⊆ A`, the intersection is just `interior A`.
  have h_eq : (A ∩ interior A : Set X) = interior A := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨(interior_subset : interior A ⊆ A) hx, hx⟩
  simpa [h_eq] using (P1_interior (X := X) (A := A))

theorem P1_of_empty_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : A = ∅) : Topology.P1 (X:=X) A := by
  simpa [hA] using (P1_empty (X := X))

theorem P3_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) : Topology.P3 (X:=X) (closure A) := by
  -- Unfold the definition of `P3`
  unfold Topology.P3
  intro x hx
  -- Every point lies in `univ`
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  -- Rewrite using `h.closure_eq` and simplify
  simpa [h.closure_eq, closure_closure, interior_univ] using hx_univ

theorem P3_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A = interior (closure A)) : Topology.P3 (X:=X) A := by
  -- Unfold the definition of `P3`
  unfold Topology.P3
  intro x hx
  -- `x` lies in the closure of `A`
  have hx_cl : (x : X) ∈ closure A := subset_closure hx
  -- Rewrite using the provided equality
  simpa using (h ▸ hx_cl)

theorem P2_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (X:=X) (Aᶜ) := by
  simpa using
    (P2_of_open (X := X) (A := Aᶜ) ((isOpen_compl_iff).2 hA))

theorem exists_minimal_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Topology.P1 (X:=X) A ∧ ∀ B : Set X, B ⊆ A → Topology.P1 (X:=X) B → B = A := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · simpa using (Topology.P1_empty (X := X))
  · intro B hB_subset _hB_P1
    have h_eq : (B : Set X) = ∅ := by
      apply Set.Subset.antisymm hB_subset
      exact Set.empty_subset _
    simpa using h_eq

theorem P2_iff_P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (interior A)) : Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  constructor
  · intro hP2
    exact Topology.P3_of_P2 (A := A) hP2
  · intro _hP3
    exact Topology.P2_of_dense_interior (X := X) (A := A) hA

theorem exists_open_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ U : Set X, IsOpen U ∧ Topology.P3 (X:=X) U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, ?_⟩
  simpa using (P3_univ (X := X))

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hDense : Dense A) : Topology.P2 (X:=X) A := by
  -- Since `A` is closed and dense, it must be the whole space
  have hAU : (A : Set X) = (Set.univ : Set X) := by
    have : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
    simpa [hA.closure_eq] using this
  -- Conclude using the already proved `P2` for `univ`
  simpa [hAU] using (P2_univ (X := X))

theorem exists_open_dense_P1 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ U : Set X, IsOpen U ∧ Dense U ∧ Topology.P1 (X:=X) U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, ?_⟩
  simpa using (P1_univ (X := X))

theorem exists_compact_P3 {X : Type*} [TopologicalSpace X] [CompactSpace X] : ∃ K : Set X, IsCompact K ∧ Topology.P3 (X:=X) K := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using isCompact_univ
  · simpa using (P3_univ (X := X))

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (X:=X) A ↔ closure A ⊆ closure (interior A) := by
  unfold Topology.P1
  constructor
  · intro h
    simpa [closure_closure] using (closure_mono h)
  · intro h
    exact subset_trans (subset_closure : (A : Set X) ⊆ closure A) h

theorem exists_closed_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsClosed A ∧ Topology.P1 (X:=X) A := by
  refine ⟨(Set.univ : Set X), isClosed_univ, ?_⟩
  simpa using (P1_univ (X := X))

theorem P1_relatively_open {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) (hB : Topology.P1 (X:=X) B) : Topology.P1 (X:=X) (A ∩ B) := by
  classical
  -- Unpack the hypothesis for `B`
  unfold Topology.P1 at hB
  -- Unfold the goal
  unfold Topology.P1
  intro x hx
  -- Split the membership information
  have hxA : x ∈ A := hx.1
  have hxB : x ∈ B := hx.2
  -- From `P1 B`
  have hx_clB : x ∈ closure (interior B) := hB hxB
  -- Auxiliary membership
  have hx_aux : x ∈ (A ∩ closure (interior B) : Set X) := by
    exact ⟨hxA, hx_clB⟩
  -- Key inclusion:  `A ∩ closure (interior B) ⊆ closure (A ∩ interior B)`
  have h_subset :
      (A ∩ closure (interior B) : Set X) ⊆ closure (A ∩ interior B) := by
    intro y hy
    rcases hy with ⟨hyA, hyCl⟩
    -- Show `y ∈ closure (A ∩ interior B)`
    have : y ∈ closure (A ∩ interior B) := by
      refine (mem_closure_iff).2 ?_
      intro V hV_open hyV
      -- `V ∩ A` is an open neighbourhood of `y`
      have hVA_open : IsOpen (V ∩ A) := hV_open.inter hA
      have hyVA : y ∈ V ∩ A := ⟨hyV, hyA⟩
      -- Intersect with `interior B` using `hyCl`
      have h_nonempty : ((V ∩ A) ∩ interior B : Set X).Nonempty :=
        (mem_closure_iff).1 hyCl (V ∩ A) hVA_open hyVA
      -- Rearrange the intersection
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using h_nonempty
    exact this
  -- Obtain membership in the intermediate closure
  have hx_cl_aux : x ∈ closure (A ∩ interior B) := h_subset hx_aux
  -- `A ∩ interior B ⊆ interior (A ∩ B)`
  have h_subset2 :
      (A ∩ interior B : Set X) ⊆ interior (A ∩ B) := by
    -- Openness
    have h_open : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    -- Inclusion
    have h_sub : (A ∩ interior B : Set X) ⊆ (A ∩ B) := by
      intro y hy
      exact ⟨hy.1, (interior_subset : interior B ⊆ B) hy.2⟩
    -- Use maximality of the interior
    exact interior_maximal h_sub h_open
  -- Pass to closures
  have h_subset2_cl :
      closure (A ∩ interior B) ⊆ closure (interior (A ∩ B)) :=
    closure_mono h_subset2
  -- Finish
  exact h_subset2_cl hx_cl_aux

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : (Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A) := (P1_iff_P3_of_open (X:=X) (A:=A) hA).trans
    (P3_iff_P2_of_open (X:=X) (A:=A) hA)

theorem P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) : Topology.P2 (X:=X) A := by
  classical
  -- Unfold the definition of `P2`
  unfold Topology.P2
  intro x hx
  -- In a discrete topology every set is open
  have hA_open : IsOpen (A : Set X) := by
    simpa using (isOpen_discrete (s := A))
  -- Hence `interior A = A`
  have hInt : interior A = A := hA_open.interior_eq
  -- View `hx` as a membership in `interior A`
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hx
  -- Use monotonicity of `interior`
  have h_subset :
      (interior A : Set X) ⊆ interior (closure (interior A)) := by
    simpa using
      (interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)))
  exact h_subset hxInt

theorem P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {U : Set Y} (hU : IsOpen U) : Topology.P1 (X:=X) (f ⁻¹' U) := by
  -- `f ⁻¹' U` is open since `f` is continuous and `U` is open
  have hOpen : IsOpen (f ⁻¹' U) := hU.preimage hf
  -- apply the lemma for open sets
  exact P1_of_open (X := X) (A := f ⁻¹' U) hOpen

theorem exists_disjoint_P3 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A B : Set X, A ∩ B = ∅ ∧ Topology.P3 (X:=X) A ∧ Topology.P3 (X:=X) B := by
  refine ⟨(∅ : Set X), (Set.univ : Set X), ?_, ?_, ?_⟩
  · simp
  · simpa using (Topology.P3_empty (X := X))
  · simpa using (Topology.P3_univ (X := X))

theorem exists_nonempty_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, A.Nonempty ∧ Topology.P2 (X:=X) A := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact ⟨x₀, by simp⟩
  · simpa using (P2_univ (X := X))