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


theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact fun x hx =>
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hP2 hx)

theorem exists_subset_P2 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · intro x hx
    cases hx
  · intro x hx
    cases hx

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_clA : x ∈ closure (interior A : Set X) := hA hxA
      have h_sub : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h_set : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_set
        exact closure_mono h_int
      exact h_sub hx_clA
  | inr hxB =>
      have hx_clB : x ∈ closure (interior B : Set X) := hB hxB
      have h_sub : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h_set : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_set
        exact closure_mono h_int
      exact h_sub hx_clB

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ interior (closure (interior A))`
      have hx_intA : x ∈ interior (closure (interior (A : Set X))) := hA hxA
      -- show this set is contained in the required one
      have h_subset :
          interior (closure (interior (A : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) := by
        -- step 1: `interior A ⊆ interior (A ∪ B)`
        have h_int_sub : interior (A : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        -- step 2: take closures
        have h_cl_sub :
            closure (interior (A : Set X))
              ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_sub
        -- step 3: take interiors again
        exact interior_mono h_cl_sub
      exact h_subset hx_intA
  | inr hxB =>
      -- `x ∈ interior (closure (interior B))`
      have hx_intB : x ∈ interior (closure (interior (B : Set X))) := hB hxB
      -- analogous inclusion for `B`
      have h_subset :
          interior (closure (interior (B : Set X)))
            ⊆ interior (closure (interior (A ∪ B))) := by
        have h_int_sub : interior (B : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        have h_cl_sub :
            closure (interior (B : Set X))
              ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_sub
        exact interior_mono h_cl_sub
      exact h_subset hx_intB

theorem P1_iff_closure_inter_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
    · -- `closure A ⊆ closure (interior A)`
      have h : (A : Set X) ⊆ closure (interior A) := hP1
      have h' : closure (A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono h
      simpa [closure_closure] using h'
  · intro h_eq
    -- Need to show `A ⊆ closure (interior A)`
    intro x hx
    have : x ∈ closure (A : Set X) := subset_closure hx
    simpa [h_eq] using this

theorem exists_open_subset_P3 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ U ⊆ A ∧ P3 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (interior_maximal subset_closure isOpen_interior)

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ interior (closure A)`
      have hxIntClA : x ∈ interior (closure (A : Set X)) := hA hxA
      -- show this set is contained in the required one
      have h_subset :
          interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) := by
        -- step 1: `A ⊆ A ∪ B`
        have h_set : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        -- step 2: take closures
        have h_closure : closure (A : Set X) ⊆ closure (A ∪ B) :=
          closure_mono h_set
        -- step 3: take interiors
        exact interior_mono h_closure
      exact h_subset hxIntClA
  | inr hxB =>
      -- `x ∈ interior (closure B)`
      have hxIntClB : x ∈ interior (closure (B : Set X)) := hB hxB
      -- analogous inclusion for `B`
      have h_subset :
          interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) := by
        have h_set : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        have h_closure : closure (B : Set X) ⊆ closure (A ∪ B) :=
          closure_mono h_set
        exact interior_mono h_closure
      exact h_subset hxIntClB

theorem closure_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior (closure (interior A))) ⊆ closure A := by
  -- First, prove `interior (closure (interior A)) ⊆ closure A`
  have h :
      interior (closure (interior A)) ⊆ closure (A : Set X) := by
    calc
      interior (closure (interior A))
          ⊆ closure (interior A) := interior_subset
      _ ⊆ closure A := by
        exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Then take closures of both sides and use `closure_closure`
  simpa [closure_closure] using (closure_mono h)

theorem exists_max_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P1 B ∧ (∀ C : Set X, B ⊆ C → C ⊆ A → P1 C → C = B) := by
  classical
  -- `E` is the family of all subsets of `A` that satisfy `P1`.
  let E : Set (Set X) := {B | (B ⊆ A) ∧ P1 B}
  -- `B` is the union of all sets in `E`.
  let B : Set X := ⋃₀ E

  -- Step 1:  `B ⊆ A`.
  have hBsubsetA : (B : Set X) ⊆ A := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCmem, hxC⟩
    have hCsubA : (C : Set X) ⊆ A := by
      have h := hCmem
      dsimp [E] at h
      exact h.1
    exact hCsubA hxC

  -- Step 2:  `P1 B`.
  have hBP1 : P1 B := by
    intro x hxB
    rcases Set.mem_sUnion.1 hxB with ⟨C, hCmem, hxC⟩
    -- `C` itself satisfies `P1`.
    have hC_P1 : P1 (C : Set X) := by
      have h := hCmem
      dsimp [E] at h
      exact h.2
    have hx_clC : x ∈ closure (interior (C : Set X)) := hC_P1 hxC
    -- `C ⊆ B`
    have hCsubB : (C : Set X) ⊆ B := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨C, hCmem, hy⟩
    -- Monotonicity of `interior` and `closure`.
    have h_int_mono : interior (C : Set X) ⊆ interior B :=
      interior_mono hCsubB
    have h_cl_mono :
        closure (interior (C : Set X)) ⊆ closure (interior B) :=
      closure_mono h_int_mono
    exact h_cl_mono hx_clC

  -- Step 3:  maximality of `B`.
  have hMax :
      ∀ C : Set X, B ⊆ C → C ⊆ A → P1 C → C = B := by
    intro C hBC hCA hP1C
    -- `C` is also in `E`, hence `C ⊆ B`.
    have hCmem : C ∈ E := by
      dsimp [E]
      exact And.intro hCA hP1C
    have hCsubB : C ⊆ B := by
      intro x hxC
      exact Set.mem_sUnion.2 ⟨C, hCmem, hxC⟩
    exact subset_antisymm hCsubB hBC

  -- Assemble the result.
  exact ⟨B, hBsubsetA, hBP1, hMax⟩

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hA_open
  exact interior_maximal subset_closure hA_open

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono
      (closure_mono (interior_subset : (interior A : Set X) ⊆ A))
  exact h_subset hx'

theorem P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 (closure A) := by
  intro hP2
  -- Obtain `A ⊆ interior (closure A)` from `P2 A`
  have hSub : (A : Set X) ⊆ interior (closure A) := by
    have hP3 : P3 A := P2_imp_P3 hP2
    simpa using hP3
  -- Conclude `closure A ⊆ closure (interior (closure A))`
  exact fun x hx => (closure_mono hSub) hx

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  exact P3_of_open isOpen_interior

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} : (∀ B, B ∈ 𝒮 → P1 B) → P1 (⋃₀ 𝒮) := by
  intro h𝒮
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBmem, hxB⟩
  have hP1B : P1 (B : Set X) := h𝒮 B hBmem
  have hx_clB : x ∈ closure (interior (B : Set X)) := hP1B hxB
  have h_subset : closure (interior (B : Set X)) ⊆ closure (interior (⋃₀ 𝒮)) := by
    have h_int_subset : interior (B : Set X) ⊆ interior (⋃₀ 𝒮) := by
      have h_subset_set : (B : Set X) ⊆ ⋃₀ 𝒮 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨B, hBmem, hy⟩
      exact interior_mono h_subset_set
    exact closure_mono h_int_subset
  exact h_subset hx_clB

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsub :
      (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  have hx' : x ∈ interior (closure (interior A)) := hsub hx
  simpa [interior_interior] using hx'

theorem P2_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 (closure (interior A)) := by
  intro hP2
  intro x hx
  have hx_clA : x ∈ closure (A : Set X) :=
    (closure_mono (interior_subset : (interior A : Set X) ⊆ A)) hx
  have h_clA_subset : closure (A : Set X) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hP2
  exact h_clA_subset hx_clA

theorem closure_inter_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) ⊆ closure A := by
  intro _
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} : (∀ B ∈ 𝒮, P2 B) → P2 (⋃₀ 𝒮) := by
  intro h𝒮
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBmem, hxB⟩
  have hP2B : P2 (B : Set X) := h𝒮 B hBmem
  have hx_intB : x ∈ interior (closure (interior (B : Set X))) := hP2B hxB
  have h_subset :
      interior (closure (interior (B : Set X)))
        ⊆ interior (closure (interior (⋃₀ 𝒮))) := by
    have h_int_sub : interior (B : Set X) ⊆ interior (⋃₀ 𝒮) := by
      have h_sub : (B : Set X) ⊆ ⋃₀ 𝒮 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨B, hBmem, hy⟩
      exact interior_mono h_sub
    have h_cl_sub :
        closure (interior (B : Set X))
          ⊆ closure (interior (⋃₀ 𝒮)) :=
      closure_mono h_int_sub
    exact interior_mono h_cl_sub
  exact h_subset hx_intB

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒮 : Set (Set X)} : (∀ B ∈ 𝒮, P3 B) → P3 (⋃₀ 𝒮) := by
  intro h𝒮
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨B, hBmem, hxB⟩
  have hP3B : P3 (B : Set X) := h𝒮 B hBmem
  have hx_intClB : x ∈ interior (closure (B : Set X)) := hP3B hxB
  have h_subset :
      interior (closure (B : Set X)) ⊆ interior (closure (⋃₀ 𝒮)) := by
    have h_closure : closure (B : Set X) ⊆ closure (⋃₀ 𝒮) := by
      have h_sub : (B : Set X) ⊆ ⋃₀ 𝒮 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨B, hBmem, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_intClB

theorem exists_closed_superset_P1 {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, A ⊆ C ∧ IsClosed C ∧ P1 C := by
  refine ⟨Set.univ, ?_, isClosed_univ, ?_⟩
  · exact Set.subset_univ A
  · intro x hx
    simpa [interior_univ, closure_univ] using hx

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`
  have h₁ : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hP1)
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior (A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h_int
  exact h₂ (h₁ hx)

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P2 A := by
  intro hA_open
  intro x hx
  have h_subset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA_open
  have hx' : x ∈ interior (closure A) := h_subset hx
  simpa [hA_open.interior_eq] using hx'

theorem P2_imp_closure_inter_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact (P1_iff_closure_inter_eq).1 (P2_imp_P1 hP2)

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense A → P3 A := by
  intro hDense
  intro x hx
  have hInt : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    have hCl : closure (A : Set X) = (Set.univ : Set X) :=
      (dense_iff_closure_eq).1 hDense
    simpa [hCl, interior_univ]
  simpa [hInt]

theorem exists_max_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P2 B ∧ (∀ C : Set X, B ⊆ C → C ⊆ A → P2 C → C = B) := by
  classical
  -- `E` is the family of all subsets of `A` that satisfy `P2`.
  let E : Set (Set X) := {B | (B ⊆ A) ∧ P2 B}
  -- `B` is the union of all sets in `E`.
  let B : Set X := ⋃₀ E
  -- Step 1:  `B ⊆ A`.
  have hBsubsetA : (B : Set X) ⊆ A := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCmem, hxC⟩
    dsimp [E] at hCmem
    exact hCmem.1 hxC
  -- Step 2:  `P2 B`.
  have hBP2 : P2 B := by
    have hFam : ∀ C ∈ E, P2 C := by
      intro C hCmem
      dsimp [E] at hCmem
      exact hCmem.2
    simpa [B] using (P2_sUnion hFam)
  -- Step 3:  maximality of `B`.
  have hMax :
      ∀ C : Set X, B ⊆ C → C ⊆ A → P2 C → C = B := by
    intro C hBC hCA hP2C
    -- `C` is also in `E`, hence `C ⊆ B`.
    have hCmem : C ∈ E := by
      dsimp [E]
      exact And.intro hCA hP2C
    have hCsubB : (C : Set X) ⊆ B := by
      intro x hxC
      exact Set.mem_sUnion.2 ⟨C, hCmem, hxC⟩
    exact subset_antisymm hCsubB hBC
  -- Assemble the result.
  exact ⟨B, hBsubsetA, hBP2, hMax⟩

theorem exists_min_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P3 B ∧ (∀ C : Set X, C ⊆ B → P3 C → C = B) := by
  refine ⟨(∅ : Set X), ?_, ?_, ?_⟩
  · intro x hx
    cases hx
  · intro x hx
    cases hx
  · intro C hCsubset _hP3C
    apply Set.Subset.antisymm hCsubset
    exact Set.empty_subset _

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem exists_open_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ U ⊆ A ∧ P1 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (P1_interior (A := A))

theorem exists_closed_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, A ⊆ C ∧ IsClosed C ∧ P3 C := by
  refine ⟨Set.univ, ?_, isClosed_univ, ?_⟩
  · exact Set.subset_univ A
  · exact P3_univ

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P3 A → P2 A := by
  intro hP1 hP3
  intro x hxA
  -- First, show the closures of `A` and `interior A` coincide.
  have h_closure_subset : closure (A : Set X) ⊆ closure (interior A) := by
    simpa [closure_closure] using (closure_mono hP1)
  have h_subset' : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  have h_closure_eq : closure (interior A) = closure (A : Set X) :=
    subset_antisymm h_subset' h_closure_subset
  -- Use `P3` together with the equality of closures to obtain the desired result.
  have hx_in : x ∈ interior (closure (A : Set X)) := hP3 hxA
  simpa [h_closure_eq] using hx_in

theorem exists_open_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ U ⊆ A ∧ P2 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (P2_interior (A := A))

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA_open
  intro x hx
  have : x ∈ closure (A : Set X) := subset_closure hx
  simpa [hA_open.interior_eq] using this

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A ↔ P1 A ∧ P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_imp_P1 hP2, P2_imp_P3 hP2⟩
  · rintro ⟨hP1, hP3⟩
    exact P2_of_P1_and_P3 hP1 hP3

theorem P3_of_dense_inter {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P3 A := by
  intro hDense
  intro x hxA
  -- `closure (interior A)` is the whole space
  have hClInt : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (dense_iff_closure_eq).1 hDense
  -- hence `closure A` is also the whole space
  have h_subset : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  have h_univ_sub : (Set.univ : Set X) ⊆ closure A := by
    simpa [hClInt] using h_subset
  have h_closure_sub : closure (A : Set X) ⊆ (Set.univ : Set X) :=
    Set.subset_univ _
  have hClA : closure (A : Set X) = (Set.univ : Set X) :=
    subset_antisymm h_closure_sub h_univ_sub
  -- therefore the interior of `closure A` is the whole space
  have hx_in : (x : X) ∈ interior (closure (A : Set X)) := by
    have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hClA, interior_univ] using hx_univ
  exact hx_in

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense A → P2 A := by
  intro hClosed hDense
  -- First, show that `A = univ`
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      (dense_iff_closure_eq).1 hDense
    have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
    simpa [h_closure_eq] using h_closure
  -- Reduce to the already proved case `P2_univ`
  simpa [hA_univ] using (P2_univ : P2 (Set.univ : Set X))

theorem P1_inter_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ A ∩ closure (interior A) = A := by
  classical
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · intro x hx
      exact hx.1
    · intro x hxA
      exact ⟨hxA, hP1 hxA⟩
  · intro hEq
    exact (Set.inter_eq_left).1 hEq

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P2 (s i)) → P2 (⋃ i, s i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hP2i : P2 (s i) := hP2 i
  have hx_int : x ∈ interior (closure (interior (s i))) := hP2i hx_i
  have h_subset :
      interior (closure (interior (s i)))
        ⊆ interior (closure (interior (⋃ j, s j))) := by
    -- Step 1: `interior (s i) ⊆ interior (⋃ j, s j)`
    have h_int_sub : interior (s i) ⊆ interior (⋃ j, s j) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    -- Step 2: take closures
    have h_cl_sub :
        closure (interior (s i))
          ⊆ closure (interior (⋃ j, s j)) :=
      closure_mono h_int_sub
    -- Step 3: take interiors again
    exact interior_mono h_cl_sub
  exact h_subset hx_int

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P3 (s i)) → P3 (⋃ i, s i) := by
  intro hP3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hP3i : P3 (s i) := hP3 i
  have hx_int : x ∈ interior (closure (s i : Set X)) := hP3i hx_i
  have h_subset :
      interior (closure (s i : Set X))
        ⊆ interior (closure (⋃ j, s j)) := by
    have h_closure :
        closure (s i : Set X) ⊆ closure (⋃ j, s j) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_int

theorem exists_min_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B ∧ (∀ C, C ⊆ B → P1 C → C = B) := by
  refine ⟨(∅ : Set X), Set.empty_subset _, P1_empty, ?_⟩
  intro C hCsubset _hP1C
  exact subset_antisymm hCsubset (Set.empty_subset _)

theorem P1_imp_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  exact (P1_iff_closure_inter_eq).1

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P1 (s i)) → P1 (⋃ i, s i) := by
  intro hP1
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hP1i : P1 (s i) := hP1 i
  have hx_cl : x ∈ closure (interior (s i : Set X)) := hP1i hx_i
  have h_subset :
      closure (interior (s i : Set X))
        ⊆ closure (interior (⋃ j, s j)) := by
    have h_int_sub : interior (s i : Set X) ⊆ interior (⋃ j, s j) := by
      have h_sub : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    exact closure_mono h_int_sub
  exact h_subset hx_cl

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P2 A := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have hUniv : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (dense_iff_closure_eq).1 hDense
  -- Hence `P1 A` holds.
  have hP1 : P1 A := by
    intro x hx
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [hUniv] using this
  -- `P3 A` follows from density.
  have hP3 : P3 A := P3_of_dense_inter hDense
  -- Conclude `P2 A`.
  exact P2_of_P1_and_P3 hP1 hP3

theorem P1_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense A → P1 A := by
  intro hClosed hDense
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      (dense_iff_closure_eq).1 hDense
    have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
    simpa [h_closure_eq] using h_closure
  simpa [hA_univ] using (P1_univ : P1 (Set.univ : Set X))

theorem exists_P3_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ B, B ⊆ A ∧ P3 B := by
  intro _hP1
  refine ⟨interior A, interior_subset, ?_⟩
  simpa using (P3_interior (A := A))

theorem exists_P1_superset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → ∃ B, A ⊆ B ∧ P1 B := by
  intro hP3
  refine ⟨interior (closure (A : Set X)), ?_, ?_⟩
  · -- `A ⊆ interior (closure A)`
    exact hP3
  · -- `P1 (interior (closure A))`
    simpa using (P1_interior (A := closure (A : Set X)))

theorem P1_exists_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P1_empty⟩

theorem P2_exists_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P2_empty⟩

theorem P1_iff_interior_union_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ interior A ∪ closure (interior A) = closure A := by
  classical
  constructor
  · intro hP1
    -- `h_eq` is the equality of closures coming from `P1`
    have h_eq : closure (interior A) = closure A :=
      (P1_iff_closure_inter_eq).1 hP1
    -- `interior A` is contained in `closure (interior A)`
    have h_union : interior A ∪ closure (interior A) = closure (interior A) :=
      (Set.union_eq_right.2
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)))
    -- put the two equalities together
    simpa [h_union] using h_eq
  · intro hUnion
    -- first inclusion: `closure (interior A) ⊆ closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- second inclusion: `closure A ⊆ closure (interior A)`
    have h₂ : closure A ⊆ closure (interior A) := by
      intro x hx
      -- rewrite membership using `hUnion`
      have hx_union : x ∈ interior A ∪ closure (interior A) := by
        simpa [hUnion] using hx
      cases hx_union with
      | inl hInt => exact subset_closure hInt
      | inr hCl  => exact hCl
    -- deduce equality of closures
    have h_eq : closure (interior A) = closure A :=
      Set.Subset.antisymm h₁ h₂
    -- conclude `P1 A`
    exact (P1_iff_closure_inter_eq).2 h_eq

theorem exists_P2_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, Set.subset_univ A, ?_⟩
  simpa using (P2_univ : P2 (Set.univ : Set X))

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P1 A → P1 (f '' A) := by
  intro hP1
  intro y hy
  -- pick a preimage point `x : X` with `f x = y`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the required closure
  have hx_cl : (x : X) ∈ closure (interior (A : Set X)) := hP1 hxA
  -- map this membership with `f`
  have h_mem_img : (f x : Y) ∈ f '' closure (interior (A : Set X)) :=
    ⟨x, hx_cl, rfl⟩
  -- `f` sends closures to closures
  have h_img_eq :
      f '' closure (interior (A : Set X)) =
        closure (f '' interior (A : Set X)) := by
    simpa using f.image_closure (s := interior (A : Set X))
  have h2 : (f x : Y) ∈ closure (f '' interior (A : Set X)) := by
    simpa [h_img_eq] using h_mem_img
  -- `f` sends interiors to interiors
  have h_int_eq :
      f '' interior (A : Set X) = interior (f '' A) := by
    simpa using f.image_interior (s := A)
  -- rewrite and conclude
  have : (f x : Y) ∈ closure (interior (f '' A)) := by
    simpa [h_int_eq] using h2
  exact this

theorem exists_dense_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : (∃ B, Dense B ∧ B ⊆ A) → ∃ B, B ⊆ A ∧ P1 B := by
  intro _
  exact ⟨(∅ : Set X), Set.empty_subset _, P1_empty⟩

theorem exists_closed_P2_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, A ⊆ C ∧ IsClosed C ∧ P2 C := by
  refine ⟨(Set.univ : Set X), Set.subset_univ A, isClosed_univ, ?_⟩
  exact P2_univ

theorem P1_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hp
  -- Split the point `p` and the membership conditions.
  rcases p with ⟨x, y⟩
  change (x, y) ∈ Set.prod A B at hp
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Use the `P1` hypotheses on the two coordinates.
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have hy_cl : y ∈ closure (interior B) := hP1B hyB
  ------------------------------------------------------------------
  -- 1.  Show `(x, y)` belongs to `closure (interior A ×ˢ interior B)`.
  ------------------------------------------------------------------
  have h_mem_closure_S :
      (x, y) ∈ closure (Set.prod (interior A) (interior B)) := by
    -- First, note that `(x, y)` lies in the product of the two closures.
    have h_in_prod :
        (x, y) ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
      And.intro hx_cl hy_cl
    -- Identify that product with the required closure.
    have h_cl_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod (interior A) (interior B)) =
            closure (interior A) ×ˢ closure (interior B))
    simpa [h_cl_eq] using h_in_prod
  ------------------------------------------------------------------
  -- 2.  `interior A ×ˢ interior B` sits inside `interior (A ×ˢ B)`.
  ------------------------------------------------------------------
  have hS_open : IsOpen (Set.prod (interior A) (interior B)) :=
    isOpen_interior.prod isOpen_interior
  have hS_sub : Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
    intro q hq
    exact And.intro
      ((interior_subset : interior A ⊆ A) hq.1)
      ((interior_subset : interior B ⊆ B) hq.2)
  have hS_sub_int :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) :=
    interior_maximal hS_sub hS_open
  ------------------------------------------------------------------
  -- 3.  Take closures and conclude.
  ------------------------------------------------------------------
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B))
        ⊆ closure (interior (Set.prod A B)) :=
    closure_mono hS_sub_int
  exact h_closure_subset h_mem_closure_S

theorem P2_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hp
  -- Split the point `p` into its coordinates.
  rcases p with ⟨x, y⟩
  change (x, y) ∈ Set.prod A B at hp
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply the `P2` hypotheses on the two coordinates.
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hy_int : y ∈ interior (closure (interior B)) := hP2B hyB
  --------------------------------------------------------------------------------
  -- `S` is the product of the two open neighbourhoods obtained above.
  --------------------------------------------------------------------------------
  let S :=
    Set.prod (interior (closure (interior A))) (interior (closure (interior B)))
  have h_mem_S : (x, y) ∈ (S : Set (X × Y)) := by
    dsimp [S]; exact And.intro hx_int hy_int
  -- `S` is open.
  have hS_open : IsOpen (S : Set (X × Y)) := by
    dsimp [S]
    exact isOpen_interior.prod isOpen_interior
  --------------------------------------------------------------------------------
  -- 1.  Show that `S ⊆ closure (interior (A ×ˢ B))`.
  --------------------------------------------------------------------------------
  have hS_sub_closure :
      (S : Set (X × Y)) ⊆ closure (interior (Set.prod A B)) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate lies in the appropriate closure.
    have hq1_cl :
        q.1 ∈ closure (interior A) :=
      (interior_subset :
          interior (closure (interior A)) ⊆ closure (interior A)) hq1
    have hq2_cl :
        q.2 ∈ closure (interior B) :=
      (interior_subset :
          interior (closure (interior B)) ⊆ closure (interior B)) hq2
    have h_in_prod_cl :
        (q : X × Y) ∈
          Set.prod (closure (interior A)) (closure (interior B)) :=
      And.intro hq1_cl hq2_cl
    -- Identify the previous product with a closure of a product.
    have h_closure_prod_eq :
        closure (Set.prod (interior A) (interior B)) =
          Set.prod (closure (interior A)) (closure (interior B)) := by
      simpa using closure_prod_eq
    have hq_in_closure_prod :
        (q : X × Y) ∈ closure (Set.prod (interior A) (interior B)) := by
      simpa [h_closure_prod_eq] using h_in_prod_cl
    -- `interior A ×ˢ interior B` sits inside `interior (A ×ˢ B)`.
    have hT_sub :
        Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
      -- Use `interior_maximal`.
      have hT_open :
          IsOpen (Set.prod (interior A) (interior B)) :=
        isOpen_interior.prod isOpen_interior
      have hT_subset :
          Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
        intro z hz
        exact And.intro
          ((interior_subset : interior A ⊆ A) hz.1)
          ((interior_subset : interior B ⊆ B) hz.2)
      exact interior_maximal hT_subset hT_open
    have h_closure_mono :
        closure (Set.prod (interior A) (interior B))
          ⊆ closure (interior (Set.prod A B)) :=
      closure_mono hT_sub
    exact h_closure_mono hq_in_closure_prod
  --------------------------------------------------------------------------------
  -- 2.  Since `S` is open and contained in the previous closure, it is contained
  --     in the interior of that closure.
  --------------------------------------------------------------------------------
  have hS_sub_inner :
      (S : Set (X × Y)) ⊆ interior (closure (interior (Set.prod A B))) :=
    interior_maximal hS_sub_closure hS_open
  --------------------------------------------------------------------------------
  -- 3.  Conclude.
  --------------------------------------------------------------------------------
  exact hS_sub_inner h_mem_S

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P3 A → P3 (f '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of the closure of `A`
  have hx_int : (x : X) ∈ interior (closure (A : Set X)) := hP3 hxA
  -- map this membership through `f`
  have h_mem_img : (f x : Y) ∈ f '' interior (closure (A : Set X)) :=
    ⟨x, hx_int, rfl⟩
  -- `f` sends interiors to interiors
  have h_img_int :
      f '' interior (closure (A : Set X)) =
        interior (f '' closure (A : Set X)) := by
    simpa using f.image_interior (s := closure (A : Set X))
  have h1 : (f x : Y) ∈ interior (f '' closure (A : Set X)) := by
    simpa [h_img_int] using h_mem_img
  -- `f` sends closures to closures
  have h_img_cl :
      f '' closure (A : Set X) = closure (f '' A) := by
    simpa using f.image_closure (s := A)
  -- rewrite and conclude
  have : (f x : Y) ∈ interior (closure (f '' A)) := by
    simpa [h_img_cl] using h1
  exact this

theorem P3_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hp
  -- Split the point `p` into its coordinates.
  rcases p with ⟨x, y⟩
  change (x, y) ∈ Set.prod A B at hp
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply the `P3` hypotheses on the two coordinates.
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3A hxA
  have hy_int : y ∈ interior (closure (B : Set Y)) := hP3B hyB
  ----------------------------------------------------------------------
  -- An open neighbourhood of `(x, y)` lying inside the desired interior.
  ----------------------------------------------------------------------
  let S : Set (X × Y) :=
    Set.prod (interior (closure (A : Set X))) (interior (closure (B : Set Y)))
  have h_mem_S : (x, y) ∈ (S : Set (X × Y)) := by
    dsimp [S]; exact And.intro hx_int hy_int
  have hS_open : IsOpen (S : Set (X × Y)) := by
    dsimp [S]; exact isOpen_interior.prod isOpen_interior
  ----------------------------------------------------------------------
  -- Show that `S` is contained in `closure (A ×ˢ B)`.
  ----------------------------------------------------------------------
  have hS_sub_closure : (S : Set (X × Y)) ⊆ closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate lies in the respective closure.
    have hq1_cl : q.1 ∈ closure (A : Set X) :=
      (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hq1
    have hq2_cl : q.2 ∈ closure (B : Set Y) :=
      (interior_subset : interior (closure (B : Set Y)) ⊆ closure (B : Set Y)) hq2
    have hq_prod : (q : X × Y) ∈
        Set.prod (closure (A : Set X)) (closure (B : Set Y)) :=
      And.intro hq1_cl hq2_cl
    -- Identify this product with the required closure via `closure_prod_eq`.
    have h_eq :
        closure (Set.prod A B) =
          Set.prod (closure (A : Set X)) (closure (B : Set Y)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod A B) =
            closure (A : Set X) ×ˢ closure (B : Set Y))
    simpa [h_eq] using hq_prod
  ----------------------------------------------------------------------
  -- Since `S` is open, it is contained in the interior of that closure.
  ----------------------------------------------------------------------
  have hS_sub_int :
      (S : Set (X × Y)) ⊆ interior (closure (Set.prod A B)) :=
    interior_maximal hS_sub_closure hS_open
  ----------------------------------------------------------------------
  -- Conclude.
  ----------------------------------------------------------------------
  exact hS_sub_int h_mem_S

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P2 A → P2 (f '' A) := by
  intro hP2
  -- Obtain `P1` and `P3` for `A` from `P2 A`.
  have hP1A : P1 A := P2_imp_P1 hP2
  have hP3A : P3 A := P2_imp_P3 hP2
  -- Transport these properties through the homeomorphism.
  have hP1_image : P1 (f '' A) := P1_image_homeomorph f hP1A
  have hP3_image : P3 (f '' A) := P3_image_homeomorph f hP3A
  -- Combine them to get `P2` for `f '' A`.
  exact (P2_iff_P1_and_P3).2 ⟨hP1_image, hP3_image⟩

theorem P2_empty_iff_true {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P2_empty

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (f ⁻¹' B) := by
  intro hP1B
  -- Transport `P1` through the inverse homeomorphism.
  have h : P1 (f.symm '' B) := P1_image_homeomorph f.symm hP1B
  -- Show that `f.symm '' B` coincides with `f ⁻¹' B`.
  have h_eq : (f.symm '' B : Set X) = f ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      change f (f.symm y) ∈ B
      simpa [f.apply_symm_apply] using hyB
    · intro hx
      exact ⟨f x, hx, by
        simpa using f.symm_apply_apply x⟩
  simpa [h_eq] using h

theorem exists_compact_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P3 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P3_empty⟩

theorem exists_max_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P3 B ∧ (∀ C : Set X, B ⊆ C → C ⊆ A → P3 C → C = B) := by
  classical
  -- `E` is the collection of subsets of `A` satisfying `P3`.
  let E : Set (Set X) := {B | (B ⊆ A) ∧ P3 B}
  -- `B` is the union of all sets in `E`.
  let B : Set X := ⋃₀ E
  -- First, show `B ⊆ A`.
  have hBsubsetA : (B : Set X) ⊆ A := by
    intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCmem, hxC⟩
    dsimp [E] at hCmem
    exact hCmem.1 hxC
  -- Next, show `P3 B`.
  have hBP3 : P3 B := by
    have hFam : ∀ C ∈ E, P3 C := by
      intro C hCmem
      dsimp [E] at hCmem
      exact hCmem.2
    simpa [B] using (P3_sUnion hFam)
  -- Finally, establish maximality of `B`.
  have hMax :
      ∀ C : Set X, B ⊆ C → C ⊆ A → P3 C → C = B := by
    intro C hBC hCA hP3C
    -- `C` is an element of `E`, hence contained in `B`.
    have hCmem : C ∈ E := by
      dsimp [E]
      exact And.intro hCA hP3C
    have hCsubB : (C : Set X) ⊆ B := by
      intro x hxC
      exact Set.mem_sUnion.2 ⟨C, hCmem, hxC⟩
    exact Set.Subset.antisymm hCsubB hBC
  -- Assemble the result.
  exact ⟨B, hBsubsetA, hBP3, hMax⟩

theorem exists_min_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B : Set X, B ⊆ A ∧ P2 B ∧ (∀ C : Set X, C ⊆ B → P2 C → C = B) := by
  refine ⟨(∅ : Set X), Set.empty_subset _, P2_empty, ?_⟩
  intro C hCsubset _hP2C
  exact subset_antisymm hCsubset (Set.empty_subset _)

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P1 A → P1 (Set.prod A (Set.univ : Set Y)) := by
  intro hP1A
  have hP1Univ : P1 (Set.univ : Set Y) := P1_univ
  simpa using (P1_product (A := A) (B := (Set.univ : Set Y)) hP1A hP1Univ)

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P2 A → P2 (Set.prod A (Set.univ : Set Y)) := by
  intro hP2A
  simpa using
    (P2_product (A := A) (B := (Set.univ : Set Y)) hP2A
      (by
        simpa using (P2_univ : P2 (Set.univ : Set Y))))

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hP3A
  have hP3Univ : P3 (Set.univ : Set Y) := P3_univ
  simpa using (P3_product (A := A) (B := (Set.univ : Set Y)) hP3A hP3Univ)

theorem P2_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP3
  intro x hxA
  -- From `P3 A` we have `x ∈ interior (closure A)`.
  have hx_int_closureA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Since `A` is closed, `closure A = A`.
  have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
  -- Therefore `x ∈ interior A`.
  have hx_intA : x ∈ interior (A : Set X) := by
    simpa [h_closure_eq] using hx_int_closureA
  -- `interior A` is open and contained in `closure (interior A)`,
  -- hence it is contained in `interior (closure (interior A))`.
  have h_subset :
      interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact h_subset hx_intA

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (f ⁻¹' B) := by
  intro hP2B
  -- First transport `P2` through the inverse homeomorphism.
  have h : P2 (f.symm '' B) := by
    simpa using (P2_image_homeomorph (f := f.symm) (A := B) hP2B)
  -- Show that this image is exactly the preimage we are interested in.
  have h_eq : (f.symm '' B : Set X) = f ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      change f (f.symm y) ∈ B
      simpa [f.apply_symm_apply] using hyB
    · intro hx
      exact ⟨f x, hx, by
        simpa using f.symm_apply_apply x⟩
  -- Rewrite along the obtained equality.
  simpa [h_eq] using h

theorem P1_finset_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : Finset ι) (u : ι → Set X) : (∀ i, i ∈ s → P1 (u i)) → P1 (⋃ i ∈ s, u i) := by
  intro hP1
  intro x hx
  -- Decompose the membership in the finite union.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hi, hxui⟩
  -- `P1` holds for `u i`.
  have hP1i : P1 (u i) := hP1 i hi
  have hx_cl : x ∈ closure (interior (u i : Set X)) := hP1i hxui
  -- Show the required inclusion of closures.
  have h_subset :
      closure (interior (u i : Set X))
        ⊆ closure (interior (⋃ j ∈ s, u j)) := by
    -- First, the corresponding inclusion for interiors.
    have h_int_subset :
        interior (u i : Set X)
          ⊆ interior (⋃ j ∈ s, u j) := by
      have h_set_subset : (u i : Set X) ⊆ ⋃ j ∈ s, u j := by
        intro y hy
        exact
          Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, hy⟩⟩
      exact interior_mono h_set_subset
    -- Take closures.
    exact closure_mono h_int_subset
  exact h_subset hx_cl

theorem P2_finset_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : Finset ι) (u : ι → Set X) : (∀ i, i ∈ s → P2 (u i)) → P2 (⋃ i ∈ s, u i) := by
  intro hP2
  intro x hx
  -- Decompose the membership in the finite union.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hi, hxui⟩
  -- `P2` holds for `u i`.
  have hP2i : P2 (u i) := hP2 i hi
  have hx_int : x ∈ interior (closure (interior (u i : Set X))) := hP2i hxui
  -- Show the required inclusion of the interiors of the closures.
  have h_subset :
      interior (closure (interior (u i : Set X))) ⊆
        interior (closure (interior (⋃ j ∈ s, u j))) := by
    -- Step 1: `interior (u i) ⊆ interior (⋃ j ∈ s, u j)`.
    have h_int_sub :
        interior (u i : Set X) ⊆ interior (⋃ j ∈ s, u j) := by
      have h_set_sub : (u i : Set X) ⊆ ⋃ j ∈ s, u j := by
        intro y hy
        exact
          Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, hy⟩⟩
      exact interior_mono h_set_sub
    -- Step 2: take closures.
    have h_cl_sub :
        closure (interior (u i : Set X)) ⊆
          closure (interior (⋃ j ∈ s, u j)) :=
      closure_mono h_int_sub
    -- Step 3: take interiors again.
    exact interior_mono h_cl_sub
  exact h_subset hx_int

theorem P3_finset_iUnion {X : Type*} [TopologicalSpace X] {ι} (s : Finset ι) (u : ι → Set X) : (∀ i, i ∈ s → P3 (u i)) → P3 (⋃ i ∈ s, u i) := by
  intro hP3
  intro x hx
  -- Break membership in the finite union into its constituents.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
  -- Apply `P3` to the chosen index.
  have hP3i : P3 (u i) := hP3 i hi
  have hx_int : x ∈ interior (closure (u i : Set X)) := hP3i hxi
  -- Show that the corresponding interior is included in the one for the union.
  have h_subset :
      interior (closure (u i : Set X)) ⊆
        interior (closure (⋃ j ∈ s, u j)) := by
    -- First, the inclusion for closures.
    have h_closure_sub :
        closure (u i : Set X) ⊆ closure (⋃ j ∈ s, u j) := by
      have h_set_sub : (u i : Set X) ⊆ ⋃ j ∈ s, u j := by
        intro y hy
        exact
          Set.mem_iUnion.2
            ⟨i, Set.mem_iUnion.2 ⟨hi, hy⟩⟩
      exact closure_mono h_set_sub
    -- Then apply monotonicity of `interior`.
    exact interior_mono h_closure_sub
  exact h_subset hx_int

theorem exists_dense_P2_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ Dense B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ A, dense_univ, ?_⟩
  simpa using (P2_univ : P2 (Set.univ : Set X))

theorem exists_open_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, Set.subset_univ A, ?_⟩
  simpa using (P3_univ : P3 (Set.univ : Set X))

theorem exists_closed_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, IsClosed C ∧ C ⊆ A ∧ P1 C := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, P1_empty⟩

theorem isOpen_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → IsOpen A := by
  intro hClosed hP2
  -- `P2 A` gives `A ⊆ interior (closure (interior A))`.
  have h1 : (A : Set X) ⊆ interior (closure (interior A)) := hP2
  -- Since `A` is closed, `closure (interior A) ⊆ A`.
  have h2 : closure (interior (A : Set X)) ⊆ A := by
    have h : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [hClosed.closure_eq] using h
  -- Hence `interior (closure (interior A)) ⊆ interior A`.
  have h3 :
      interior (closure (interior (A : Set X))) ⊆ interior A :=
    interior_mono h2
  -- Combine inclusions to get `A ⊆ interior A`.
  have h4 : (A : Set X) ⊆ interior A := fun x hx => h3 (h1 hx)
  -- Together with `interior_subset`, this yields equality.
  have h_eq : interior A = A := Set.Subset.antisymm interior_subset h4
  -- Conclude that `A` is open.
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h_eq] using this

theorem P1_empty_iff_true {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P1_empty

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} : (∀ i, P2 (s i)) → P2 (⋃ i, s i) := by
  exact P2_iUnion

theorem P1_closure_interior_any {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  -- First, note that `interior A ⊆ interior (closure (interior A))`.
  have h :
      (interior A : Set X) ⊆ interior (closure (interior A)) := by
    have :
        interior (interior (A : Set X)) ⊆
          interior (closure (interior A)) :=
      interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using this
  -- Take closures and use monotonicity to obtain the required inclusion.
  exact fun x hx => (closure_mono h) hx