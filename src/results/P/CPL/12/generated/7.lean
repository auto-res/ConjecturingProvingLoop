

namespace Topology

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {ℱ : Set (Set X)} : (∀ A, A ∈ ℱ → P3 A) → P3 (⋃₀ ℱ) := by
  intro hAll
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hA_mem, hxA⟩
  have hP3A : P3 A := hAll A hA_mem
  have hx' : x ∈ interior (closure A) := hP3A hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ ℱ)) := by
    have hcl : closure A ⊆ closure (⋃₀ ℱ) := by
      have hAsub : (A : Set X) ⊆ ⋃₀ ℱ := by
        intro y hy
        exact Set.mem_sUnion.mpr ⟨A, hA_mem, hy⟩
      exact closure_mono hAsub
    exact interior_mono hcl
  exact hsubset hx'

namespace Topology

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P2 A := by
  intro hDense
  intro x hx
  have h_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hDense, interior_univ] using h_univ

namespace Topology

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen (closure A) → P3 A := by
  intro hOpen
  intro x hx
  have hx_cl : x ∈ closure A := (subset_closure : (A : Set X) ⊆ closure A) hx
  simpa [hOpen.interior_eq] using hx_cl

namespace Topology

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P1 A := by
  intro hDense x _
  simpa [hDense] using (Set.mem_univ x)