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


theorem P2_imp_P3 {A : Set X} : P2 A → P3 A := by
  intro h x hx
  exact (interior_mono (closure_mono interior_subset)) (h hx)

theorem P2_imp_P1 {A : Set X} : P2 A → P1 A := by
  intro h x hx
  exact interior_subset (h hx)

theorem P1_univ : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ]

theorem P2_univ : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_empty : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem union_P1 {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      have h₁ : x ∈ closure (interior A) := hA hA_mem
      have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h₂ h₁
  | inr hB_mem =>
      have h₁ : x ∈ closure (interior B) := hB hB_mem
      have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h₂ h₁

theorem union_P2 {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hxA : x ∈ interior (closure (interior A)) := hA hA_mem
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- first enlarge the set inside `interior`
        have h_closure :
            closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- enlarge the set inside `closure`
          have h_int : interior A ⊆ interior (A ∪ B) := by
            -- enlarge the set inside `interior`
            have h_set : (A : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inl hy
            exact interior_mono h_set
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hB_mem =>
      -- `x ∈ B`
      have hxB : x ∈ interior (closure (interior B)) := hB hB_mem
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_closure :
            closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) := by
            have h_set : (B : Set X) ⊆ A ∪ B := by
              intro y hy
              exact Or.inr hy
            exact interior_mono h_set
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB

theorem union_P3 {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x ∈ A`
      have hxA : x ∈ interior (closure A) := hA hA_mem
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure A ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inl hy
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hB_mem =>
      -- `x ∈ B`
      have hxB : x ∈ interior (closure B) := hB hB_mem
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have h_closure : closure B ⊆ closure (A ∪ B) := by
          apply closure_mono
          intro y hy
          exact Or.inr hy
        exact interior_mono h_closure
      exact h_subset hxB

theorem P1_interior {A : Set X} : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using
    (subset_closure hx : x ∈ closure (interior A))

theorem P3_Union {ι} (s : ι → Set X) (h : ∀ i, P3 (s i)) : P3 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  have hx_int : x ∈ interior (closure (s i)) := h i hi
  have h_subset : interior (closure (s i)) ⊆ interior (closure (⋃ j, s j)) := by
    apply interior_mono
    have h_closure : closure (s i) ⊆ closure (⋃ j, s j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact h_closure
  exact h_subset hx_int

theorem P2_of_open {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hx_cl : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx_int
  simpa [hA.interior_eq] using hx_cl

theorem P3_of_open {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have h_sub : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_sub hx_int

theorem P2_sUnion {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P2 A) : P2 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := (h A hA_mem) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  have h_final :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono h_closure_subset
  exact h_final hx_int

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P1 A) : P1 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_cl : x ∈ closure (interior A) := (h A hA_mem) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝒜 := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
  have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono hA_subset
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_cl

theorem P3_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : P3 A := by
  intro x hx
  simpa [hA.closure_eq, interior_univ] using
    (by
      simp : x ∈ (Set.univ : Set X))

theorem P2_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : interior A = Set.univ) : P2 A := by
  intro x hx
  simp [hA]

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro h x hx
  -- First, use `h` to see that `closure A ⊆ closure (interior A)`,
  -- hence `x ∈ closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) := by
    have h_subset : closure A ⊆ closure (interior A) := by
      -- `closure_mono h : closure A ⊆ closure (closure (interior A))`
      -- but `closure (closure _)` simplifies to `closure _`
      simpa using (closure_mono h :
        closure A ⊆ closure (closure (interior A)))
    exact h_subset hx
  -- Next, enlarge once more: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_target :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono
      (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
  exact h_target hx₁

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  have hx_cl : x ∈ closure (interior (s i)) := (h i) hi
  have h_subset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    apply closure_mono
    have h_int : interior (s i) ⊆ interior (⋃ j, s j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact h_int
  exact h_subset hx_cl

theorem P1_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior (closure (interior A)))) := by
  -- First, `interior (closure (interior A))` satisfies `P1`
  have h₁ : P1 (interior (closure (interior A))) := by
    simpa using (P1_interior (A := closure (interior A)))
  -- Hence its closure also satisfies `P1`
  exact (P1_closure (A := interior (closure (interior A)))) h₁

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P2 (interior A) := by
  intro x hx
  have hmem : x ∈ interior (closure (interior A)) := hA (interior_subset hx)
  simpa [interior_interior] using hmem

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  have hAB : P2 (A ∪ B) := union_P2 hA hB
  exact union_P2 hAB hC

theorem P3_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : interior A = Set.univ) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA] using (by triv)
  have h_sub : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact h_sub hx_int

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  simpa [P2, P3, hA.interior_eq]

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : ι → Set X) (h : ∀ i, P2 (s i)) : P2 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  have hx_int : x ∈ interior (closure (interior (s i))) := (h i) hi
  have h_subset :
      interior (closure (interior (s i))) ⊆
        interior (closure (interior (⋃ j, s j))) := by
    apply interior_mono
    have h_closure :
        closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
      apply closure_mono
      have h_int :
          interior (s i) ⊆ interior (⋃ j, s j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact h_int
    exact h_closure
  exact h_subset hx_int

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → A ⊆ closure (interior A) := by
  intro hP2
  exact (P2_imp_P1 (A := A)) hP2

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h : ∀ A ∈ 𝒜, P3 A) : P3 (⋃₀ 𝒜) := by
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hx_int : x ∈ interior (closure A) := (h A hA_mem) hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    apply interior_mono
    have h_closure : closure A ⊆ closure (⋃₀ 𝒜) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    exact h_closure
  exact h_subset hx_int

theorem P1_and_P3_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := by
  intro x hxA
  -- `P3` gives that `x ∈ interior (closure A)`.
  have hx_int_clA : x ∈ interior (closure A) := h3 hxA
  -- From `P1` we have `A ⊆ closure (interior A)`, hence
  -- `closure A ⊆ closure (interior A)`.
  have h_cl_subset : closure A ⊆ closure (interior A) := by
    have h : (A : Set X) ⊆ closure (interior A) := h1
    simpa using closure_mono h
  -- Taking interiors preserves inclusion.
  have h_int_subset :
      interior (closure A) ⊆ interior (closure (interior A)) :=
    interior_mono h_cl_subset
  -- Apply the inclusion to obtain the desired membership.
  exact h_int_subset hx_int_clA

theorem P3_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior (closure (interior (closure A)))) := by
  apply P3_of_open
  simpa using isOpen_interior

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P2_imp_P3 hP2
  · intro hP3
    intro x hxA
    -- from `P3`, and using `closure_eq` for a closed set, we get `x ∈ interior A`
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using this
    -- `interior A ⊆ interior (closure (interior A))`
    have h_subset : interior A ⊆ interior (closure (interior A)) := by
      have h₁ : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      have h₂ := interior_mono h₁
      simpa [interior_interior] using h₂
    exact h_subset hx_intA

theorem P1_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : P1 A ↔ P2 A := by
  constructor
  · intro hP1
    have hP3 : P3 (A := A) := P3_dense (A := A) hA
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3
  · intro hP2
    exact P2_imp_P1 (A := A) hP2

theorem P1_open_iff_closure_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → (P1 A ↔ P1 (closure A)) := by
  intro hA_open
  constructor
  · intro hP1
    exact P1_closure (A := A) hP1
  · intro _
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    simpa [hA_open.interior_eq] using hx_cl

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (A := A) ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    have h₂ : closure A ⊆ closure (interior A) := by
      have h : (A : Set X) ⊆ closure (interior A) := hP1
      simpa using (closure_mono h)
    exact subset_antisymm h₁ h₂
  · intro h_eq
    intro x hx
    have hx_cl : (x : X) ∈ closure A := subset_closure hx
    simpa [h_eq] using hx_cl

theorem P1_iff_P3_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X} (hA_open : IsOpen A) (hA_closed : IsClosed A) : Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  have h_int : interior A = A := hA_open.interior_eq
  have h_cl : closure A = A := hA_closed.closure_eq
  constructor
  · intro _hP1
    intro x hx
    simpa [h_int, h_cl] using hx
  · intro _hP3
    intro x hx
    simpa [h_int, h_cl] using hx

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) (hD : Topology.P2 (A := D)) : Topology.P2 (A := A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`
  have hABC : P2 (A ∪ B ∪ C) :=
    P2_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Then add `D`
  simpa [Set.union_assoc] using
    union_P2 (A := A ∪ B ∪ C) (B := D) hABC hD

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (A := interior A) := by
  apply Topology.P3_of_open
  simpa using isOpen_interior

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (interior A)) : Topology.P3 (A := A) := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hA.closure_eq, interior_univ]
  have h_subset :
      interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact h_subset hx'

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) (hC : Topology.P3 (A := C)) (hD : Topology.P3 (A := D)) : Topology.P3 (A := A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`
  have hABC : Topology.P3 (A := A ∪ B ∪ C) := by
    -- Combine `A` and `B`
    have hAB : Topology.P3 (A := A ∪ B) :=
      Topology.union_P3 (A := A) (B := B) hA hB
    -- Add `C`
    have hABC' : Topology.P3 (A := (A ∪ B) ∪ C) :=
      Topology.union_P3 (A := A ∪ B) (B := C) hAB hC
    simpa [Set.union_assoc] using hABC'
  -- Then add `D`
  simpa [Set.union_assoc] using
    Topology.union_P3 (A := A ∪ B ∪ C) (B := D) hABC hD

theorem P1_iff_P2_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X} (hA_open : IsOpen A) (hA_closed : IsClosed A) : Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  have h1 : Topology.P1 (A := A) ↔ Topology.P3 (A := A) :=
    P1_iff_P3_of_clopen (A := A) hA_open hA_closed
  have h2 : Topology.P2 (A := A) ↔ Topology.P3 (A := A) :=
    (P2_iff_P3_of_open (A := A) hA_open)
  simpa using h1.trans h2.symm

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : Dense (interior A)) : Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro hP1
    -- From the density of `interior A` we obtain `P3 A`
    have hP3 : P3 (A := A) := P3_of_dense_interior (A := A) h_dense
    -- Combine `P1` and `P3` to get `P2`
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3
  · intro hP2
    -- `P2` always implies `P1`
    exact P2_imp_P1 (A := A) hP2

theorem P3_of_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (closure (interior A))) : Topology.P3 (A := A) := by
  intro x hx
  -- Step 1: `closure (interior A)` is dense, hence equals `univ`.
  have h_dense_eq : (closure (interior A) : Set X) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Step 2: deduce `closure A = univ`.
  have h_closureA_univ : (closure A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`.
    have h_subset : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    -- So `univ` is contained in `closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro y hy
      have : (y : X) ∈ closure (interior A) := by
        -- rewrite using `h_dense_eq`
        simpa [h_dense_eq] using hy
      exact h_subset this
    exact Set.Subset.antisymm (Set.subset_univ _) h_univ_subset
  -- Step 3: therefore `interior (closure A) = univ`.
  have h_int_eq : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closureA_univ, interior_univ]
  -- Step 4: conclude the desired membership.
  simpa [h_int_eq]

theorem P2_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) : Topology.P2 (A := Set.prod A B) := by
  intro p hp
  -- Split the membership of the point `p : X × Y`
  rcases hp with ⟨hpA, hpB⟩
  -- Use the `P2` hypotheses on the two coordinates
  have hx : p.fst ∈ interior (closure (interior A)) := hA hpA
  have hy : p.snd ∈ interior (closure (interior B)) := hB hpB
  -- Define convenient open neighbourhoods of the two coordinates
  set U : Set X := interior (closure (interior A)) with hU_def
  set V : Set Y := interior (closure (interior B)) with hV_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using isOpen_interior
  have hV_open : IsOpen V := by
    simpa [hV_def] using isOpen_interior
  have hpU : p.fst ∈ U := by
    simpa [hU_def] using hx
  have hpV : p.snd ∈ V := by
    simpa [hV_def] using hy
  -- The open rectangle around `p`
  have hpUV : p ∈ Set.prod U V := by
    exact ⟨hpU, hpV⟩
  -- `U × V ⊆ (closure (interior A)) × (closure (interior B))`
  have hU_subset : (U : Set X) ⊆ closure (interior A) := by
    intro x hx
    simpa [hU_def] using (interior_subset hx)
  have hV_subset : (V : Set Y) ⊆ closure (interior B) := by
    intro y hy
    simpa [hV_def] using (interior_subset hy)
  have hUV_subset_prodCl :
      Set.prod U V ⊆
        Set.prod (closure (interior A)) (closure (interior B)) :=
    Set.prod_mono hU_subset hV_subset
  -- Identify the product of closures with the closure of the product
  have h_prod_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using closure_prod_eq
  have hUV_subset :
      Set.prod U V ⊆ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_prod_eq] using hUV_subset_prodCl
  -- `interior A × interior B ⊆ interior (A × B)`
  have h_prod_int_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    have h_subset :
        Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨h1, h2⟩
      exact ⟨interior_subset h1, interior_subset h2⟩
    have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
      (isOpen_interior.prod isOpen_interior)
    exact interior_maximal h_subset h_open
  -- Enlarge once more to reach the desired closure
  have h_closure_mono :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_prod_int_subset
  have hUV_subset_target :
      Set.prod U V ⊆ closure (interior (Set.prod A B)) :=
    Set.Subset.trans hUV_subset h_closure_mono
  -- `U × V` is an open neighbourhood of `p`
  have h_openUV : IsOpen (Set.prod U V) :=
    hU_open.prod hV_open
  have hUV_nhds : Set.prod U V ∈ 𝓝 p :=
    h_openUV.mem_nhds hpUV
  -- Upgrade the neighbourhood using the inclusion
  have h_target_nhds :
      closure (interior (Set.prod A B)) ∈ 𝓝 p :=
    Filter.mem_of_superset hUV_nhds hUV_subset_target
  -- Conclude that `p` lies in the required interior
  have hp_int :
      p ∈ interior (closure (interior (Set.prod A B))) :=
    (mem_interior_iff_mem_nhds).2 h_target_nhds
  exact hp_int

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) : Topology.P3 (A := Set.prod A B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- use `P3` on the two coordinates
  have hx : p.fst ∈ interior (closure A) := hA hpA
  have hy : p.snd ∈ interior (closure B) := hB hpB
  -- auxiliary open neighbourhoods
  set U : Set X := interior (closure A) with hU_def
  set V : Set Y := interior (closure B) with hV_def
  have hU_open : IsOpen U := by
    simpa [hU_def] using isOpen_interior
  have hV_open : IsOpen V := by
    simpa [hV_def] using isOpen_interior
  have hpU : p.fst ∈ U := by
    simpa [hU_def] using hx
  have hpV : p.snd ∈ V := by
    simpa [hV_def] using hy
  have hpUV : p ∈ Set.prod U V := by
    exact ⟨hpU, hpV⟩
  -- inclusion towards the target closure
  have hU_subset : (U : Set X) ⊆ closure A := by
    intro x hx
    simpa [hU_def] using (interior_subset hx)
  have hV_subset : (V : Set Y) ⊆ closure B := by
    intro y hy
    simpa [hV_def] using (interior_subset hy)
  have hUV_subset_prodCl :
      Set.prod U V ⊆ Set.prod (closure A) (closure B) :=
    Set.prod_mono hU_subset hV_subset
  have h_prod_eq :
      closure (Set.prod A B) = Set.prod (closure A) (closure B) := by
    simpa using (closure_prod_eq :
      closure (Set.prod A B) = Set.prod (closure A) (closure B))
  have hUV_subset :
      Set.prod U V ⊆ closure (Set.prod A B) := by
    intro q hq
    have hq' : q ∈ Set.prod (closure A) (closure B) :=
      hUV_subset_prodCl hq
    simpa [h_prod_eq] using hq'
  -- `U × V` is an open neighbourhood of `p`
  have h_openUV : IsOpen (Set.prod U V) :=
    hU_open.prod hV_open
  have hUV_nhds : Set.prod U V ∈ 𝓝 p :=
    h_openUV.mem_nhds hpUV
  -- upgrade the neighbourhood using the inclusion
  have h_target_nhds :
      closure (Set.prod A B) ∈ 𝓝 p :=
    Filter.mem_of_superset hUV_nhds hUV_subset
  -- conclude
  exact (mem_interior_iff_mem_nhds).2 h_target_nhds

theorem P3_closed_iff_self {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 (A := A) ↔ A = interior (closure A) := by
  -- Since `A` is closed we have `closure A = A`.
  have h_closure : closure A = A := hA.closure_eq
  -- Hence `interior (closure A)` is contained in `A`.
  have h_int_subset : interior (closure A) ⊆ A := by
    intro x hx
    -- `x ∈ closure A`
    have h_mem : (x : X) ∈ closure A := interior_subset hx
    -- Rewrite using `h_closure`.
    have h_memA : x ∈ A := by
      have h_tmp := h_mem
      rw [h_closure] at h_tmp
      exact h_tmp
    exact h_memA
  -- Establish the equivalence.
  constructor
  · -- `P3 A → A = interior (closure A)`
    intro hP3
    exact Set.Subset.antisymm hP3 h_int_subset
  · -- `A = interior (closure A) → P3 A`
    intro h_eq
    intro x hx
    -- Rewrite the assumption using the given equality.
    have hx' : x ∈ interior (closure A) := by
      have h_tmp := hx
      rw [h_eq] at h_tmp
      exact h_tmp
    exact hx'

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι κ} (s : ι → κ → Set X) (h : ∀ i j, Topology.P2 (A := s i j)) : Topology.P2 (A := ⋃ i, ⋃ j, s i j) := by
  -- For each fixed `i`, the union over `j` satisfies `P2`.
  have h₁ : ∀ i, Topology.P2 (A := ⋃ j, s i j) := by
    intro i
    have hi : Topology.P2 (A := ⋃ j, s i j) :=
      P2_iUnion (s := s i) (h := fun j => h i j)
    simpa using hi
  -- Now take the union over `i`.
  have h₂ : Topology.P2 (A := ⋃ i, ⋃ j, s i j) :=
    P2_iUnion (s := fun i => ⋃ j, s i j) (h := h₁)
  simpa using h₂

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P1 (A := A)) : Topology.P1 (A := e '' A) := by
  -- We have to show: `e '' A ⊆ closure (interior (e '' A))`.
  intro y hy
  -- Obtain a preimage point `x`.
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P1` for `A`, we know `x ∈ closure (interior A)`.
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- Send this fact through the homeomorphism.
  have hx_img_cl : (e x : Y) ∈ closure (e '' interior A) := by
    -- First note `e x ∈ e '' closure (interior A)`.
    have h_mem : (e x : Y) ∈ e '' closure (interior A) := ⟨x, hx_cl, rfl⟩
    -- Identify this set with `closure (e '' interior A)`.
    have h_eq : (e '' closure (interior A) : Set Y) = closure (e '' interior A) := by
      simpa using e.image_closure (s := interior A)
    simpa [h_eq] using h_mem
  -- Enlarge the closure once more.
  have h_subset : (closure (e '' interior A) : Set Y) ⊆
      closure (interior (e '' A)) := by
    -- First, `e '' interior A ⊆ interior (e '' A)`.
    have h_sub : (e '' interior A : Set Y) ⊆ interior (e '' A) := by
      intro z hz
      -- Rewrite using `image_interior`.
      have h_eq_int : (e '' interior A : Set Y) = interior (e '' A) := by
        simpa using e.image_interior (s := A)
      simpa [h_eq_int] using hz
    -- Take closures.
    exact closure_mono h_sub
  -- Apply the inclusion.
  exact h_subset hx_img_cl

theorem exists_P1_subset_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (A := A)) : ∃ U, IsOpen U ∧ A ⊆ U ∧ Topology.P1 (A := U) := by
  refine ⟨Set.univ, isOpen_univ, ?_, P1_univ (X := X)⟩
  exact Set.subset_univ _

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) : Topology.P1 (A := Set.prod A B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P1` on the two coordinates
  have hx : p.fst ∈ closure (interior A) := hA hpA
  have hy : p.snd ∈ closure (interior B) := hB hpB
  -- Combine the information in the product space
  have h_prod_mem : p ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    ⟨hx, hy⟩
  -- Relate the product of closures with the closure of the product
  have h_prod_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using closure_prod_eq
  have hp_closure_int : p ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_prod_eq] using h_prod_mem
  -- `interior A × interior B ⊆ interior (A × B)`
  have h_int_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    have h_sub : Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
      intro q hq
      exact ⟨interior_subset hq.1, interior_subset hq.2⟩
    have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
      (isOpen_interior.prod isOpen_interior)
    exact interior_maximal h_sub h_open
  -- Taking closures preserves inclusion
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_int_subset
  -- Conclude
  exact h_closure_subset hp_closure_int

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 (A := A) := by
  intro x hx
  classical
  -- Since `X` is a subsingleton, a non-empty set must be `univ`.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      -- All points are equal, hence `y ∈ A`.
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hA_univ, interior_univ, closure_univ] using this

theorem P2_closed_iff_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (A := A) ↔ A = interior (closure (interior A)) := by
  classical
  constructor
  · intro hP2
    -- `hP2` already gives `A ⊆ interior (closure (interior A))`.
    apply Set.Subset.antisymm hP2
    intro x hx_int
    -- From the interior we move to the closure.
    have hx_cl : (x : X) ∈ closure (interior A) := interior_subset hx_int
    -- Since `A` is closed and `interior A ⊆ A`, we have
    -- `closure (interior A) ⊆ A`.
    have h_closure_subset : closure (interior A) ⊆ A := by
      have h_sub : (interior A : Set X) ⊆ A := interior_subset
      have h_cl : closure (interior A) ⊆ closure A := closure_mono h_sub
      simpa [hA.closure_eq] using h_cl
    exact h_closure_subset hx_cl
  · intro h_eq
    -- Use the assumed equality to obtain the required inclusion.
    intro x hxA
    exact (h_eq ▸ hxA)

theorem P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 (A := A)) : A ⊆ interior (closure A) := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have h_sub :
      (interior (closure (interior A)) : Set X) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono interior_subset
  exact h_sub hx'

theorem P1_prod_left_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 (A := A)) : Topology.P1 (A := Set.prod A (Set.univ : Set Y)) := by
  -- `Set.univ : Set Y` satisfies `P1`.
  have hB : Topology.P1 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P1_univ (X := Y)
  -- Apply the product lemma.
  simpa using
    (Topology.P1_prod (A := A) (B := (Set.univ : Set Y)) hA hB)

theorem P2_prod_right_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P2 (A := B)) : Topology.P2 (A := Set.prod (Set.univ : Set X) B) := by
  simpa using
    (Topology.P2_product
      (A := (Set.univ : Set X)) (B := B)
      (hA := Topology.P2_univ (X := X)) (hB := hB))

theorem exists_maximal_P2_subset {X : Type*} [TopologicalSpace X] : ∀ A : Set X, ∃ B, A ⊆ B ∧ Topology.P2 (A := B) ∧ ∀ C, B ⊆ C → Topology.P2 (A := C) → C = B := by
  intro A
  classical
  -- Define the family of `P2` supersets of `A`.
  let 𝒜 : Set (Set X) := {B | A ⊆ B ∧ Topology.P2 (A := B)}
  -- Define `B` to be the union of all sets in `𝒜`.
  let B : Set X := ⋃₀ 𝒜
  -- First, show `A ⊆ B`.
  have hAB : A ⊆ B := by
    intro x hx
    -- `Set.univ` belongs to `𝒜`.
    have h_univ_mem : (Set.univ : Set X) ∈ 𝒜 := by
      show A ⊆ (Set.univ : Set X) ∧ Topology.P2 (A := (Set.univ : Set X))
      exact ⟨Set.subset_univ _, Topology.P2_univ (X := X)⟩
    -- Hence `x` lies in the union.
    exact
      (Set.mem_sUnion.2 ⟨Set.univ, h_univ_mem, by trivial⟩ : x ∈ ⋃₀ 𝒜)
  -- Next, show that `B` satisfies `P2`.
  have hB_P2 : Topology.P2 (A := B) := by
    -- Each member of `𝒜` satisfies `P2`.
    have h_family : ∀ C ∈ 𝒜, Topology.P2 (A := C) := by
      intro C hC
      have : A ⊆ C ∧ Topology.P2 (A := C) := by
        simpa [𝒜] using hC
      exact this.2
    -- Use the `P2` lemma for unions.
    have : Topology.P2 (A := ⋃₀ 𝒜) :=
      Topology.P2_sUnion (𝒜 := 𝒜) h_family
    simpa [B] using this
  -- Finally, establish maximality of `B`.
  have h_max :
      ∀ C, B ⊆ C → Topology.P2 (A := C) → C = B := by
    intro C hBC hP2C
    -- Since `A ⊆ B ⊆ C`, we have `A ⊆ C`.
    have hAC : A ⊆ C := hAB.trans hBC
    -- Thus `C` lies in `𝒜`.
    have hC_mem : C ∈ 𝒜 := by
      show A ⊆ C ∧ Topology.P2 (A := C)
      exact ⟨hAC, hP2C⟩
    -- Every element of `C` is in `B`.
    have hCB : C ⊆ B := by
      intro x hx
      exact Set.mem_sUnion.2 ⟨C, hC_mem, hx⟩
    -- Conclude equality.
    exact Set.Subset.antisymm hCB hBC
  -- Assemble the required data.
  exact ⟨B, hAB, hB_P2, h_max⟩

theorem P2_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 (A := A)) : Topology.P2 (A := Set.prod A (Set.univ : Set Y)) := by
  simpa using
    (Topology.P2_product
      (X := X) (Y := Y)
      (A := A) (B := (Set.univ : Set Y))
      hA
      (Topology.P2_univ (X := Y)))

theorem exists_maximal_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ Topology.P1 (A := B) ∧ ∀ C, B ⊆ C → Topology.P1 (A := C) → C = B := by
  classical
  -- Define the family of `P1` supersets of `A`.
  let 𝒜 : Set (Set X) := {B | A ⊆ B ∧ Topology.P1 (A := B)}
  -- Define `B` to be the union of all sets in `𝒜`.
  let B : Set X := ⋃₀ 𝒜
  -- First, show `A ⊆ B`.
  have hAB : A ⊆ B := by
    intro x hx
    -- `Set.univ` belongs to `𝒜`.
    have h_univ_mem : (Set.univ : Set X) ∈ 𝒜 := by
      change
        A ⊆ (Set.univ : Set X) ∧ Topology.P1 (A := (Set.univ : Set X))
      exact ⟨Set.subset_univ _, Topology.P1_univ (X := X)⟩
    -- Hence `x` lies in the union.
    have hx' : x ∈ ⋃₀ 𝒜 :=
      Set.mem_sUnion.2 ⟨(Set.univ : Set X), h_univ_mem, trivial⟩
    simpa [B] using hx'
  -- Next, show that `B` satisfies `P1`.
  have hB_P1 : Topology.P1 (A := B) := by
    -- Each member of `𝒜` satisfies `P1`.
    have h_family : ∀ C, C ∈ 𝒜 → Topology.P1 (A := C) := by
      intro C hC
      have : A ⊆ C ∧ Topology.P1 (A := C) := by
        simpa [𝒜] using hC
      exact this.2
    -- Use the `P1` lemma for unions.
    have : Topology.P1 (A := ⋃₀ 𝒜) :=
      Topology.P1_sUnion (𝒜 := 𝒜) h_family
    simpa [B] using this
  -- Finally, establish maximality of `B`.
  have h_max :
      ∀ C, B ⊆ C → Topology.P1 (A := C) → C = B := by
    intro C hBC hP1C
    -- Since `A ⊆ B ⊆ C`, we have `A ⊆ C`.
    have hAC : A ⊆ C := hAB.trans hBC
    -- Thus `C` lies in `𝒜`.
    have hC_mem : C ∈ 𝒜 := by
      change A ⊆ C ∧ Topology.P1 (A := C)
      exact ⟨hAC, hP1C⟩
    -- Every element of `C` is in `B`.
    have hCB : C ⊆ B := by
      intro x hx
      have hx' : x ∈ ⋃₀ 𝒜 :=
        Set.mem_sUnion.2 ⟨C, hC_mem, hx⟩
      simpa [B] using hx'
    -- Conclude equality.
    exact Set.Subset.antisymm hCB hBC
  -- Assemble the required data.
  exact ⟨B, hAB, hB_P1, h_max⟩

theorem P1_image_homeomorph' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P1 (A := A)) : Topology.P1 (A := e.symm ⁻¹' A) := by
  -- Identify the preimage with the image of `A`.
  have hEq : (e.symm ⁻¹' A : Set Y) = e '' A := by
    ext y
    constructor
    · intro hy
      exact
        ⟨e.symm y, hy, by
          simpa using (e.apply_symm_apply y)⟩
    · intro hy
      rcases hy with ⟨x, hxA, rfl⟩
      simpa using hxA
  -- `P1` holds for `e '' A`.
  have hP1_image : Topology.P1 (A := e '' A) :=
    P1_image_homeomorph (e := e) (A := A) hA
  -- Prove the required inclusion using `hEq`.
  intro y hy
  have hy_image : y ∈ e '' A := by
    simpa [hEq] using hy
  have h_closure : y ∈ closure (interior (e '' A)) :=
    hP1_image hy_image
  simpa [hEq] using h_closure

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P2 (A := A)) : Topology.P2 (A := e '' A) := by
  intro y hy
  -- pick a preimage point
  rcases hy with ⟨x, hxA, rfl⟩
  -- `P2` for `A`
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- map through the homeomorphism, using `image_interior`
  have hx_int_image : (e x : Y) ∈ interior (e '' closure (interior A)) := by
    -- first, `e x` lies in the image of the interior
    have h_mem : (e x : Y) ∈ e '' interior (closure (interior A)) :=
      ⟨x, hx_int, rfl⟩
    have h_eq := e.image_interior (s := closure (interior A))
    simpa [h_eq] using h_mem
  -- identify the closure via `image_closure`
  have hx_int_image' : (e x : Y) ∈ interior (closure (e '' interior A)) := by
    have h_closure_eq := e.image_closure (s := interior A)
    simpa [h_closure_eq] using hx_int_image
  -- rewrite using `image_interior` once more
  have h_int_eq : (e '' interior A : Set Y) = interior (e '' A) := by
    simpa using e.image_interior (s := A)
  have hx_target : (e x : Y) ∈ interior (closure (interior (e '' A))) := by
    simpa [h_int_eq] using hx_int_image'
  exact hx_target

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P3 (A := A)) : Topology.P3 (A := e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of the closure of `A`.
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Transport this fact through the homeomorphism.
  have hx_int_image : (e x : Y) ∈ interior (e '' closure A) := by
    -- First, `e x` belongs to `e '' interior (closure A)`.
    have h_mem : (e x : Y) ∈ (e '' interior (closure A) : Set Y) :=
      ⟨x, hx_int, rfl⟩
    -- Identify this image with the desired interior.
    have h_eq : (e '' interior (closure A) : Set Y) = interior (e '' closure A) := by
      simpa using e.image_interior (s := closure A)
    simpa [h_eq] using h_mem
  -- Relate `e '' closure A` to `closure (e '' A)`.
  have h_closure_eq : (e '' closure A : Set Y) = closure (e '' A) := by
    simpa using e.image_closure (s := A)
  -- Rewrite to obtain the final membership.
  have hx_target : (e x : Y) ∈ interior (closure (e '' A)) := by
    simpa [h_closure_eq] using hx_int_image
  exact hx_target

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P1 (A := B)) : Topology.P1 (A := e ⁻¹' B) := by
  -- Identify the preimage with the image under `e.symm`.
  have hEq : (e ⁻¹' B : Set X) = (e.symm '' B) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by
        simp⟩
    · rintro ⟨y, hyB, rfl⟩
      simpa [e.apply_symm_apply] using hyB
  -- Apply the existing lemma to obtain `P1` for `e.symm '' B`.
  have hP1 : Topology.P1 (A := e.symm '' B) :=
    P1_image_homeomorph (e := e.symm) (A := B) hB
  -- Transport the property along the set equality.
  simpa [hEq] using hP1

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P2 (A := B)) : Topology.P2 (A := e ⁻¹' B) := by
  -- Identify the preimage with the image under `e.symm`.
  have hEq : (e ⁻¹' B : Set X) = e.symm '' B := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
  -- `P2` holds for `e.symm '' B`.
  have hP2_image : Topology.P2 (A := e.symm '' B) :=
    P2_image_homeomorph (e := e.symm) (A := B) hB
  -- Use this to prove the goal.
  intro x hx
  -- View `x` as an element of `e.symm '' B`.
  have hx_image : (x : X) ∈ e.symm '' B := by
    exact ⟨e x, hx, by simp⟩
  -- Apply `P2` for the image.
  have hx_target : x ∈ interior (closure (interior (e.symm '' B))) :=
    hP2_image hx_image
  -- Reinterpret through the set equality `hEq`.
  simpa [hEq] using hx_target

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} (hB : Topology.P3 (A := B)) : Topology.P3 (A := e ⁻¹' B) := by
  -- Identify the preimage with the image under `e.symm`.
  have hEq : (e ⁻¹' B : Set X) = e.symm '' B := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hyB, rfl⟩
      simpa using hyB
  -- `P3` holds for `e.symm '' B`.
  have hP3_image : Topology.P3 (A := e.symm '' B) :=
    P3_image_homeomorph (e := e.symm) (A := B) hB
  -- Transport the property using the set equality.
  simpa [P3, hEq] using hP3_image

theorem P1_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (A := A)) : closure A ⊆ closure (interior A) := by
  intro x hx
  have h' : x ∈ closure (closure (interior A)) := (closure_mono hA) hx
  simpa [closure_closure] using h'

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (h_sub : A ⊆ B) (h_dense : Dense A) : Topology.P3 (A := B) := by
  intro x hxB
  -- Step 1: the closure of `A` is the whole space.
  have h_closureA_univ : (closure (A) : Set X) = (Set.univ : Set X) := by
    simpa using h_dense.closure_eq
  -- Step 2: deduce that the closure of `B` is also the whole space.
  have h_closureB_univ : (closure (B) : Set X) = (Set.univ : Set X) := by
    -- We already know `closure A ⊆ closure B`.
    have h_subset : (closure A : Set X) ⊆ closure B := closure_mono h_sub
    -- Hence `univ ⊆ closure B`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure B := by
      intro y hy
      have : (y : X) ∈ closure A := by
        simpa [h_closureA_univ] using hy
      exact h_subset this
    exact Set.Subset.antisymm (Set.subset_univ _) h_univ_subset
  -- Step 3: `interior (closure B)` is `univ`.
  have h_int_eq : interior (closure B) = (Set.univ : Set X) := by
    simpa [h_closureB_univ, interior_univ]
  -- Step 4: the desired membership is now immediate.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int_eq] using this

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 (A := A)) : Topology.P3 (A := Set.prod A (Set.univ : Set Y)) := by
  -- `Set.univ : Set Y` satisfies `P3`.
  have hB : Topology.P3 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P3_univ (X := Y)
  simpa using
    Topology.P3_prod (A := A) (B := (Set.univ : Set Y)) hA hB

theorem P2_iterate_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (A := interior (closure (interior (closure (interior A))))) := by
  apply P2_of_open
  simpa using
    (isOpen_interior :
      IsOpen (interior (closure (interior (closure (interior A))))))

theorem P2_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 (A := A) := by
  intro x hx
  simpa [h, interior_univ]

theorem P3_of_neighbourhood_basis {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior (closure A)) : Topology.P3 (A := A) := by
  intro x hxA
  rcases h x hxA with ⟨U, _U_open, hxU, h_subset⟩
  have hx_closureU : (x : X) ∈ closure U := subset_closure hxU
  exact h_subset hx_closureU

theorem P2_seq_union {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h : ∀ n, Topology.P2 (A := A n)) : Topology.P2 (A := ⋃ n, A n) := by
  simpa using (P2_iUnion (s := A) (h := h))

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure A)) := by
  simpa using
    P2_of_open (A := interior (closure A)) isOpen_interior

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A ∧ P3 A := by
  intro h
  exact ⟨P2_imp_P1 (A := A) h, P2_imp_P3 (A := A) h⟩

theorem P2_directed_Union {X : Type*} [TopologicalSpace X] {ι : Type*} (s : ι → Set X) (hmono : ∀ i j, s i ⊆ s j ∨ s j ⊆ s i) (h : ∀ i, Topology.P2 (A := s i)) : Topology.P2 (A := ⋃ i, s i) := by
  simpa using (P2_iUnion (s := s) (h := h))

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (A := Set.prod A B) ↔ Topology.P1 (A := Set.prod B A) := by
  classical
  -- The homeomorphism swapping the coordinates.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm X Y
  ----------------------------------------------------------------
  -- 1.  The image of `A × B` under `e` is `B × A`.
  ----------------------------------------------------------------
  have h_image :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hq with ⟨hxA, hyB⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      rcases (by
        simpa [Set.prod] using hp : y ∈ B ∧ x ∈ A) with ⟨hyB, hxA⟩
      have hq : ((x, y) : X × Y) ∈ Set.prod A B := by
        simpa [Set.prod] using And.intro hxA hyB
      have : (y, x) ∈ (e '' Set.prod A B : Set (Y × X)) := by
        refine ⟨(x, y), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 2.  The image of `B × A` under `e.symm` is `A × B`.
  ----------------------------------------------------------------
  have h_image_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨y, x⟩
      rcases hq with ⟨hyB, hxA⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hxA hyB
    · intro hp
      rcases p with ⟨x, y⟩
      rcases (by
        simpa [Set.prod] using hp : x ∈ A ∧ y ∈ B) with ⟨hxA, hyB⟩
      have hq : ((y, x) : Y × X) ∈ Set.prod B A := by
        simpa [Set.prod] using And.intro hyB hxA
      have : (x, y) ∈ (e.symm '' Set.prod B A : Set (X × Y)) := by
        refine ⟨(y, x), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 3.  Transport the `P1` property along the homeomorphism.
  ----------------------------------------------------------------
  refine ⟨?_, ?_⟩
  · intro hP1
    have hImage : Topology.P1 (A := e '' Set.prod A B) :=
      P1_image_homeomorph (e := e) (A := Set.prod A B) hP1
    simpa [h_image] using hImage
  · intro hP1
    have hImage : Topology.P1 (A := e.symm '' Set.prod B A) :=
      P1_image_homeomorph (e := e.symm) (A := Set.prod B A) hP1
    simpa [h_image_symm] using hImage

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (A := closure (interior A)) := by
  exact
    (P1_closure (A := interior A)) (by
      simpa using (P1_interior (A := A)))

theorem P3_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : Topology.P3 (A := B)) : Topology.P3 (A := Set.prod (Set.univ : Set X) B) := by
  -- `Set.univ : Set X` satisfies `P3`.
  have hA : Topology.P3 (A := (Set.univ : Set X)) := by
    simpa using Topology.P3_univ (X := X)
  simpa using
    Topology.P3_prod (A := (Set.univ : Set X)) (B := B) hA hB

theorem P3_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : Dense (interior A)) : Topology.P3 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro hP3
    -- First, deduce `P1 A` from the density of `interior A`.
    have hP1 : P1 (A := A) := by
      intro x hx
      -- Since `interior A` is dense, its closure is the whole space.
      have h_closure_univ :
          (closure (interior A) : Set X) = (Set.univ : Set X) := by
        simpa using h_dense.closure_eq
      -- Hence every point lies in this closure.
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [h_closure_univ] using this
    -- Combine `P1` and the given `P3` to obtain `P2`.
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3
  · intro hP2
    exact P2_imp_P3 (A := A) hP2

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (A := Set.prod A B) ↔ Topology.P2 (A := Set.prod B A) := by
  classical
  -- The homeomorphism swapping the coordinates.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm X Y
  ----------------------------------------------------------------
  -- 1.  The image of `A × B` under `e` is `B × A`.
  ----------------------------------------------------------------
  have h_image :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hq with ⟨hxA, hyB⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      have h : y ∈ B ∧ x ∈ A := by
        simpa [Set.prod] using hp
      rcases h with ⟨hyB, hxA⟩
      have hq : ((x, y) : X × Y) ∈ Set.prod A B := by
        simpa [Set.prod] using And.intro hxA hyB
      have : (y, x) ∈ (e '' Set.prod A B : Set (Y × X)) := by
        refine ⟨(x, y), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 2.  The image of `B × A` under `e.symm` is `A × B`.
  ----------------------------------------------------------------
  have h_image_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨y, x⟩
      rcases hq with ⟨hyB, hxA⟩
      simpa [e, Homeomorph.prodComm, Set.prod] using And.intro hxA hyB
    · intro hp
      rcases p with ⟨x, y⟩
      have h : x ∈ A ∧ y ∈ B := by
        simpa [Set.prod] using hp
      rcases h with ⟨hxA, hyB⟩
      have hq : ((y, x) : Y × X) ∈ Set.prod B A := by
        simpa [Set.prod] using And.intro hyB hxA
      have : (x, y) ∈ (e.symm '' Set.prod B A : Set (X × Y)) := by
        refine ⟨(y, x), hq, ?_⟩
        simp [e, Homeomorph.prodComm]
      simpa using this
  ----------------------------------------------------------------
  -- 3.  Transport the `P2` property along the homeomorphism.
  ----------------------------------------------------------------
  refine ⟨?_, ?_⟩
  · intro hP2
    have hImage : Topology.P2 (A := e '' Set.prod A B) :=
      P2_image_homeomorph (e := e) (A := Set.prod A B) hP2
    simpa [h_image] using hImage
  · intro hP2
    have hImage : Topology.P2 (A := e.symm '' Set.prod B A) :=
      P2_image_homeomorph (e := e.symm) (A := Set.prod B A) hP2
    simpa [h_image_symm] using hImage

theorem P1_dense_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → (Topology.P1 (A := A) ↔ closure A = closure (interior A)) := by
  intro _
  simpa [eq_comm] using (P1_iff_closure_eq (A := A))

theorem P3_closed_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hclosed : IsClosed A) (h_eq : interior A = A) : Topology.P3 (A := A) := by
  intro x hx
  simpa [hclosed.closure_eq, h_eq] using hx

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 (A := A) := by
  intro x hx
  classical
  -- In a subsingleton space, a non-empty set is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hA_univ, closure_univ, interior_univ] using this

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) : Topology.P2 (A := Set.prod A (Set.prod B C)) := by
  -- First, obtain `P2` for the product `B × C` in the space `Y × Z`.
  have hBC : Topology.P2 (A := Set.prod B C) := by
    simpa using
      (Topology.P2_product (X := Y) (Y := Z) (A := B) (B := C) hB hC)
  -- Now apply the two–factor product lemma with `A` and `B × C`.
  simpa using
    (Topology.P2_product
        (X := X) (Y := Y × Z)
        (A := A) (B := Set.prod B C) hA hBC)

theorem P2_of_P1 {A : Set X} (h : P1 A) (h_open_cl : IsOpen (closure A)) : P2 A := by
  intro x hxA
  -- `x` lies in `closure A`
  have hx_closureA : (x : X) ∈ closure A := subset_closure hxA
  -- `closure A ⊆ closure (interior A)` since `A ⊆ closure (interior A)`
  have h_subset : (closure A : Set X) ⊆ closure (interior A) := by
    have hA_subset : (A : Set X) ⊆ closure (interior A) := h
    simpa using (closure_mono hA_subset)
  -- An open set contained in a set is contained in its interior
  have h_closure_in_int :
      (closure A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal h_subset h_open_cl
  exact h_closure_in_int hx_closureA

theorem P3_subset_closure {A : Set X} (hA : P3 A) : interior A ⊆ interior (closure A) := by
  intro x hx
  exact hA (interior_subset hx)

theorem P1_of_open {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  exact subset_closure hx_int

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (A := A) ↔ (Topology.P1 (A := A) ∧ Topology.P3 (A := A)) := by
  constructor
  · intro hP2
    exact P2_imp_P1_and_P3 (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) (hC : Topology.P1 (A := C)) : Topology.P1 (A := Set.prod A (Set.prod B C)) := by
  -- First, obtain `P1` for `B × C` in the space `Y × Z`.
  have hBC : Topology.P1 (A := Set.prod B C) := by
    simpa using
      (Topology.P1_prod (A := B) (B := C) hB hC)
  -- Now combine `A` with `B × C`.
  simpa using
    (Topology.P1_prod (A := A) (B := Set.prod B C) hA hBC)

theorem P2_prod_three_univ_left {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {B : Set Y} {C : Set Z} (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) : Topology.P2 (A := Set.prod (Set.univ : Set X) (Set.prod B C)) := by
  -- First, obtain `P2` for the product `B × C` in the space `Y × Z`.
  have hBC : Topology.P2 (A := Set.prod B C) := by
    simpa using
      (Topology.P2_product
        (X := Y) (Y := Z)
        (A := B) (B := C)
        (hA := hB) (hB := hC))
  -- Now combine `Set.univ` with `B × C`.
  simpa using
    (Topology.P2_product
      (X := X) (Y := Y × Z)
      (A := (Set.univ : Set X)) (B := Set.prod B C)
      (hA := Topology.P2_univ (X := X))
      (hB := hBC))

theorem P3_iff_P1_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) (h_dense : Dense A) : Topology.P3 (A := A) ↔ Topology.P1 (A := A) := by
  simpa using
    ((P2_iff_P3_of_open (A := A) h_open).symm.trans
      ((P1_iff_P2_of_dense (A := A) h_dense).symm))

theorem P3_product_three_univ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (hA : Topology.P3 (A := (Set.univ : Set X))) (hB : Topology.P3 (A := (Set.univ : Set Y))) (hC : Topology.P3 (A := (Set.univ : Set Z))) : Topology.P3 (A := Set.prod (Set.univ : Set X) (Set.prod (Set.univ : Set Y) (Set.univ : Set Z))) := by
  -- First, build `P3` for the product of the two universal sets in `Y` and `Z`.
  have hBC : Topology.P3 (A := Set.prod (Set.univ : Set Y) (Set.univ : Set Z)) := by
    simpa using
      (Topology.P3_prod
        (A := (Set.univ : Set Y))
        (B := (Set.univ : Set Z))
        hB hC)
  -- Now take the product with the universal set in `X`.
  simpa using
    (Topology.P3_prod
      (A := (Set.univ : Set X))
      (B := Set.prod (Set.univ : Set Y) (Set.univ : Set Z))
      hA hBC)

theorem P1_exists_compact_subset {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : Set X} (hA : Topology.P1 (A := A)) : ∃ K, IsCompact K ∧ K ⊆ A := by
  classical
  by_cases hA_empty : (A : Set X) = ∅
  · refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
    simpa [hA_empty] using (Set.empty_subset (A : Set X))
  · have hA_nonempty : (A : Set X).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨x, hxA⟩
    refine ⟨({x} : Set X), isCompact_singleton, ?_⟩
    intro y hy
    have : y = x := by
      simpa [Set.mem_singleton_iff] using hy
    simpa [this] using hxA

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 (A := A)) (hB : IsClosed B) : Topology.P2 (A := A \ B) := by
  intro x hx
  -- Decompose the membership of `x`.
  rcases hx with ⟨hxA, hx_notB⟩
  -- `P2` for `A` gives a first open neighbourhood of `x`.
  have hx_intA : x ∈ interior (closure (interior A)) := hA hxA
  -- Some handy open sets.
  have hB_open   : IsOpen (Bᶜ) := hB.isOpen_compl
  have hI_open   : IsOpen (interior (closure (interior A))) := isOpen_interior
  -- The open set around `x` that we shall use.
  have hW_open : IsOpen (Bᶜ ∩ interior (closure (interior A))) :=
    hB_open.inter hI_open
  have hxW : x ∈ (Bᶜ ∩ interior (closure (interior A))) :=
    ⟨hx_notB, hx_intA⟩
  -- Main inclusion: this open neighbourhood is contained in the target closure.
  have h_subset :
      (Bᶜ ∩ interior (closure (interior A)) : Set X) ⊆
        closure (interior (A \ B)) := by
    intro y hy
    -- Split the information carried by `hy`.
    have hy_notB : y ∈ Bᶜ := hy.1
    have hy_int   : y ∈ interior (closure (interior A)) := hy.2
    -- Hence `y` also lies in `closure (interior A)`.
    have hy_clA : y ∈ closure (interior A) := interior_subset hy_int
    -- We first show that `y ∈ closure (interior A ∩ Bᶜ)`.
    have hy_clABc : y ∈ closure (interior A ∩ Bᶜ) := by
      -- Characterise membership in the closure via neighbourhoods.
      apply (mem_closure_iff).2
      intro o ho_open hy_in_o
      -- Shrink the neighbourhood inside `Bᶜ`.
      have ho_open' : IsOpen (o ∩ Bᶜ) := ho_open.inter hB_open
      have hy_in_o' : y ∈ o ∩ Bᶜ := ⟨hy_in_o, hy_notB⟩
      -- Because `y ∈ closure (interior A)`, this smaller neighbourhood
      -- meets `interior A`.
      have h_nonempty :
          ((o ∩ Bᶜ) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hy_clA _ ho_open' hy_in_o'
      -- Re-arrange the intersections to obtain the required form.
      have : (o ∩ (interior A ∩ Bᶜ)).Nonempty := by
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h_nonempty
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using this
    -- `interior A ∩ Bᶜ` is an open subset of `A \ B`,
    -- hence is contained in its interior.
    have h_int_subset :
        (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) := by
      -- It is open:
      have h_open : IsOpen (interior A ∩ Bᶜ) :=
        isOpen_interior.inter hB_open
      -- And it is contained in `A \ B`.
      have h_sub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz; exact ⟨interior_subset hz.1, hz.2⟩
      exact interior_maximal h_sub h_open
    -- Taking closures preserves inclusion.
    have h_closure_subset :
        closure (interior A ∩ Bᶜ : Set X) ⊆
          closure (interior (A \ B)) :=
      closure_mono h_int_subset
    -- Finally, put everything together.
    exact h_closure_subset hy_clABc
  -- `x` lies in an open neighbourhood contained in the target set,
  -- hence is in its interior.
  have hx_target :
      x ∈ interior (closure (interior (A \ B))) :=
    (interior_maximal h_subset hW_open) hxW
  exact hx_target

theorem P1_union_inf {X : Type*} [TopologicalSpace X] {ι : Type*} (s : ι → Set X) (h : ∀ i, Topology.P1 (A := s i)) : Topology.P1 (A := ⋃ i, ⋂ j, s i ∪ s j) := by
  intro x hx
  -- Choose an index `i` such that
  --   x ∈ ⋂ j, (s i ∪ s j)
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- From this, taking `j = i`, we deduce `x ∈ s i`.
  have hx_si : x ∈ s i := by
    have : x ∈ (s i ∪ s i) := (Set.mem_iInter.1 hx_i) i
    simpa [Set.union_self] using this
  -- Apply `P1` for the chosen set `s i`.
  have hx_cl_si : x ∈ closure (interior (s i)) := h i hx_si
  ------------------------------------------------------------------
  -- We now show that   closure (interior (s i)) ⊆ closure (interior U),
  -- where               U = ⋃ i, ⋂ j, (s i ∪ s j).
  ------------------------------------------------------------------
  -- First, `s i ⊆ U`.
  have h_si_subset_U :
      (s i : Set X) ⊆ ⋃ i, ⋂ j, (s i ∪ s j) := by
    intro y hy
    -- `y` belongs to every `s i ∪ s j`, since it is in `s i`.
    have hy_inter : y ∈ ⋂ j, (s i ∪ s j) := by
      refine Set.mem_iInter.2 ?_
      intro j; exact Or.inl hy
    exact Set.mem_iUnion.2 ⟨i, hy_inter⟩
  -- Hence, the same inclusion holds for interiors.
  have h_int_subset :
      (interior (s i) : Set X) ⊆
        interior (⋃ i, ⋂ j, (s i ∪ s j)) :=
    interior_mono h_si_subset_U
  -- Taking closures preserves inclusion.
  have h_cl_subset :
      (closure (interior (s i)) : Set X) ⊆
        closure (interior (⋃ i, ⋂ j, (s i ∪ s j))) :=
    closure_mono h_int_subset
  -- Conclude.
  exact h_cl_subset hx_cl_si

theorem P1_bigUnion₂ {X : Type*} [TopologicalSpace X] {ι κ} (s : ι → κ → Set X) (h : ∀ i j, Topology.P1 (A := s i j)) : Topology.P1 (A := ⋃ i, ⋃ j, s i j) := by
  -- First, for each fixed `i`, the union over `j` satisfies `P1`.
  have h₁ : ∀ i, Topology.P1 (A := ⋃ j, s i j) := by
    intro i
    have : Topology.P1 (A := ⋃ j, s i j) :=
      Topology.P1_Union (s := s i) (h := fun j => h i j)
    simpa using this
  -- Then take the union over `i`.
  have h₂ : Topology.P1 (A := ⋃ i, ⋃ j, s i j) :=
    Topology.P1_Union (s := fun i => ⋃ j, s i j) (h := h₁)
  simpa using h₂

theorem P3_of_closed_ball {X : Type*} [MetricSpace X] {x : X} {r : ℝ} : Topology.P3 (A := Metric.ball x r) := by
  apply Topology.P3_of_open
  simpa using isOpen_ball

theorem P2_iterate_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (A := interior (interior A)) := by
  apply P2_of_open
  simpa using isOpen_interior

theorem P2_prod_five {W Y Z : Type*} [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P2 (A := A)) (hB : P2 B) (hC : Topology.P2 (A := C)) (hD : Topology.P2 (A := D)) : Topology.P2 (A := Set.prod A (Set.prod B (Set.prod C D))) := by
  -- First, build `P2` for the auxiliary product `B × (C × D)`.
  have hBCD : Topology.P2 (A := Set.prod B (Set.prod C D)) := by
    simpa using
      (Topology.P2_prod_three
        (A := B) (B := C) (C := D)
        (hA := hB) (hB := hC) (hC := hD))
  -- Then combine it with `A`.
  simpa using
    (Topology.P2_product
      (A := A)
      (B := Set.prod B (Set.prod C D))
      hA
      hBCD)

theorem P3_closed_complement {A : Set X} (hA : IsClosed A) : P3 Aᶜ := by
  apply P3_of_open
  simpa using hA.isOpen_compl

theorem P3_prod_four_univ {Y Z W : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W] : P3 (Set.prod (Set.univ : Set X) (Set.prod (Set.univ : Set Y) (Set.prod (Set.univ : Set Z) (Set.univ : Set W)))) := by
  -- Each factor `Set.univ` satisfies `P3`.
  have hX : Topology.P3 (A := (Set.univ : Set X)) := by
    simpa using Topology.P3_univ (X := X)
  have hY : Topology.P3 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P3_univ (X := Y)
  have hZ : Topology.P3 (A := (Set.univ : Set Z)) := by
    simpa using Topology.P3_univ (X := Z)
  have hW : Topology.P3 (A := (Set.univ : Set W)) := by
    simpa using Topology.P3_univ (X := W)
  -- Build `P3` for `Z × W`.
  have hZW :
      Topology.P3 (A := Set.prod (Set.univ : Set Z) (Set.univ : Set W)) :=
    Topology.P3_prod
      (A := (Set.univ : Set Z)) (B := (Set.univ : Set W)) hZ hW
  -- Build `P3` for `Y × (Z × W)`.
  have hY_ZW :
      Topology.P3
        (A := Set.prod (Set.univ : Set Y)
              (Set.prod (Set.univ : Set Z) (Set.univ : Set W))) :=
    Topology.P3_prod
      (A := (Set.univ : Set Y))
      (B := Set.prod (Set.univ : Set Z) (Set.univ : Set W)) hY hZW
  -- Finally, build the desired product with `X`.
  simpa using
    (Topology.P3_prod
      (A := (Set.univ : Set X))
      (B := Set.prod (Set.univ : Set Y)
            (Set.prod (Set.univ : Set Z) (Set.univ : Set W)))
      hX hY_ZW)

theorem P2_prod_iterated {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) : Topology.P2 (A := Set.prod (Set.prod A B) C) := by
  -- Step 1: obtain `P2` for `A × B` in the product space `X × Y`.
  have hAB : Topology.P2 (A := Set.prod A B) := by
    simpa using
      (Topology.P2_product
        (X := X) (Y := Y)
        (A := A) (B := B)
        (hA := hA) (hB := hB))
  -- Step 2: combine this with `C`, viewed in the space `Z`.
  simpa using
    (Topology.P2_product
      (X := X × Y) (Y := Z)
      (A := Set.prod A B) (B := C)
      (hA := hAB) (hB := hC))

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) : closure A ∪ closure B ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- 1. `closure A ⊆ closure (interior A)`
      have h₁ : (closure (A) : Set X) ⊆ closure (interior A) := by
        have hA_subset : (A : Set X) ⊆ closure (interior A) := hA
        have h_cl : closure (A : Set X) ⊆ closure (closure (interior A)) :=
          closure_mono hA_subset
        simpa [closure_closure] using h_cl
      -- 2. `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have h₂ : (closure (interior A) : Set X) ⊆
          closure (interior (A ∪ B)) := by
        have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact closure_mono h_int
      exact h₂ (h₁ hxA)
  | inr hxB =>
      -- 1. `closure B ⊆ closure (interior B)`
      have h₁ : (closure (B) : Set X) ⊆ closure (interior B) := by
        have hB_subset : (B : Set X) ⊆ closure (interior B) := hB
        have h_cl : closure (B : Set X) ⊆ closure (closure (interior B)) :=
          closure_mono hB_subset
        simpa [closure_closure] using h_cl
      -- 2. `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have h₂ : (closure (interior B) : Set X) ⊆
          closure (interior (A ∪ B)) := by
        have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact closure_mono h_int
      exact h₂ (h₁ hxB)

theorem P2_imp_P1_or_P3 {A : Set X} : P2 A → (P1 A ∨ P3 A) := by
  intro h
  exact Or.inl (P2_imp_P1 (A := A) h)

theorem P3_open_inter {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) : P3 (A ∩ B) := by
  simpa using P3_of_open (A := A ∩ B) (hA := hA.inter hB)

theorem P2_Union_closed {X ι : Type*} [TopologicalSpace X] (s : ι → Set X) (hcl : ∀ i, IsClosed (s i)) (hP : ∀ i, Topology.P2 (A := s i)) : Topology.P2 (A := ⋃ i, s i) := by
  simpa using P2_iUnion (s := s) (h := hP)

theorem P2_prod_both_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : Topology.P2 (A := Set.prod (Set.univ : Set X) (Set.univ : Set Y)) := by
  simpa using
    (Topology.P2_product
      (X := X) (Y := Y)
      (A := (Set.univ : Set X)) (B := (Set.univ : Set Y))
      (hA := Topology.P2_univ (X := X))
      (hB := Topology.P2_univ (X := Y)))

theorem P2_prod_union_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 (A := A)) : Topology.P2 (A := Set.prod (A ∪ Set.univ) (Set.univ : Set Y)) := by
  simpa [Set.union_univ] using (P2_prod_both_univ (X := X) (Y := Y))

theorem P2_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) : Topology.P3 (A := A) → Topology.P2 (A := A) := by
  intro hP3
  exact (P2_iff_P3_of_closed (A := A) h_closed).mpr hP3

theorem P1_prod_five {U V W Y Z : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set U} {B : Set V} {C : Set W} {D : Set Y} {E : Set Z} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) (hC : Topology.P1 (A := C)) (hD : Topology.P1 (A := D)) (hE : Topology.P1 (A := E)) : Topology.P1 (A := Set.prod A (Set.prod B (Set.prod C (Set.prod D E)))) := by
  -- First, obtain `P1` for `D × E` in the space `Y × Z`.
  have hDE : Topology.P1 (A := Set.prod D E) := by
    simpa using
      (Topology.P1_prod (A := D) (B := E) hD hE)
  -- Next, build `P1` for `C × (D × E)` in the space `W × (Y × Z)`.
  have hCDE : Topology.P1 (A := Set.prod C (Set.prod D E)) := by
    simpa using
      (Topology.P1_prod (A := C) (B := Set.prod D E) hC hDE)
  -- Then, construct `P1` for `B × (C × (D × E))` in the space
  -- `V × (W × (Y × Z))`.
  have hBCDE :
      Topology.P1 (A := Set.prod B (Set.prod C (Set.prod D E))) := by
    simpa using
      (Topology.P1_prod
        (A := B) (B := Set.prod C (Set.prod D E)) hB hCDE)
  -- Finally, combine with `A` to obtain the desired five–fold product.
  simpa using
    (Topology.P1_prod
      (A := A) (B := Set.prod B (Set.prod C (Set.prod D E))) hA hBCDE)

theorem P2_subset_closure_interior_closure {A : Set X} (hA : P2 A) : closure A ⊆ closure (interior (closure A)) := by
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    P2_subset_interior_closure (A := A) hA
  simpa using (closure_mono h_subset)

theorem P1_closed_complement {A : Set X} (hA : IsClosed A) : P1 Aᶜ := by
  exact P1_of_open (A := Aᶜ) hA.isOpen_compl

theorem P3_prod_five_univ {X Y Z W V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V] : Topology.P3 (A := Set.prod (Set.univ : Set X) (Set.prod (Set.univ : Set Y) (Set.prod (Set.univ : Set Z) (Set.prod (Set.univ : Set W) (Set.univ : Set V))))) := by
  -- Each factor `Set.univ` satisfies `P3`.
  have hX : Topology.P3 (A := (Set.univ : Set X)) := by
    simpa using Topology.P3_univ (X := X)
  have hY : Topology.P3 (A := (Set.univ : Set Y)) := by
    simpa using Topology.P3_univ (X := Y)
  have hZ : Topology.P3 (A := (Set.univ : Set Z)) := by
    simpa using Topology.P3_univ (X := Z)
  have hW : Topology.P3 (A := (Set.univ : Set W)) := by
    simpa using Topology.P3_univ (X := W)
  have hV : Topology.P3 (A := (Set.univ : Set V)) := by
    simpa using Topology.P3_univ (X := V)
  -- Build `P3` for `W × V`.
  have hWV :
      Topology.P3 (A := Set.prod (Set.univ : Set W) (Set.univ : Set V)) :=
    Topology.P3_prod
      (A := (Set.univ : Set W)) (B := (Set.univ : Set V)) hW hV
  -- Build `P3` for `Z × (W × V)`.
  have hZ_WV :
      Topology.P3
        (A := Set.prod (Set.univ : Set Z)
              (Set.prod (Set.univ : Set W) (Set.univ : Set V))) :=
    Topology.P3_prod
      (A := (Set.univ : Set Z))
      (B := Set.prod (Set.univ : Set W) (Set.univ : Set V))
      hZ hWV
  -- Build `P3` for `Y × (Z × (W × V))`.
  have hY_ZWV :
      Topology.P3
        (A := Set.prod (Set.univ : Set Y)
              (Set.prod (Set.univ : Set Z)
                (Set.prod (Set.univ : Set W) (Set.univ : Set V)))) :=
    Topology.P3_prod
      (A := (Set.univ : Set Y))
      (B := Set.prod (Set.univ : Set Z)
            (Set.prod (Set.univ : Set W) (Set.univ : Set V)))
      hY hZ_WV
  -- Finally, combine with `X`.
  simpa using
    (Topology.P3_prod
      (A := (Set.univ : Set X))
      (B := Set.prod (Set.univ : Set Y)
            (Set.prod (Set.univ : Set Z)
              (Set.prod (Set.univ : Set W) (Set.univ : Set V))))
      hX hY_ZWV)

theorem P2_comp_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 (A := A) := by
  have hP1 : P1 (A := A) := P1_subsingleton (A := A)
  have hP3 : P3 (A := A) := P3_subsingleton (A := A)
  exact P1_and_P3_imp_P2 (A := A) hP1 hP3