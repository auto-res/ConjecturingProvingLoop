

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P3 (interior A) := by
  intro _hP3
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    simpa using
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  exact hsubset hx

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P2 A) → P2 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hPA : P2 A := hAll A hA_mem
  have hx' : x ∈ interior (closure (interior A)) := hPA hxA
  have hsubset :
      interior (closure (interior A)) ⊆ interior (closure (interior (⋃₀ ℱ))) := by
    have hInt : interior A ⊆ interior (⋃₀ ℱ) := by
      have hAsub : (A : Set X) ⊆ ⋃₀ ℱ := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact interior_mono hAsub
    have hcl : closure (interior A) ⊆ closure (interior (⋃₀ ℱ)) :=
      closure_mono hInt
    exact interior_mono hcl
  exact hsubset hx'

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hA
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hx_int