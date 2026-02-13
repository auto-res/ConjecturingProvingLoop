

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx1 : x ∈ interior (closure A) := hP3A hxA
      have hsubset : closure A ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono hsubset) hx1
  | inr hxB =>
      have hx1 : x ∈ interior (closure B) := hP3B hxB
      have hsubset : closure B ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact (interior_mono hsubset) hx1

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} : (∀ A ∈ 𝓢, Topology.P3 A) → Topology.P3 (⋃₀ 𝓢) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hx1 : x ∈ interior (closure (A : Set X)) := hP3 A hAS hxA
  have hsubset_closure : closure (A : Set X) ⊆ closure (⋃₀ (𝓢 : Set (Set X))) := by
    apply closure_mono
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
  have hsubset :
      interior (closure (A : Set X)) ⊆ interior (closure (⋃₀ (𝓢 : Set (Set X)))) :=
    interior_mono hsubset_closure
  exact hsubset hx1

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝓢 : Set (Set X)} : (∀ A ∈ 𝓢, Topology.P2 A) → Topology.P2 (⋃₀ 𝓢) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨A, hAS, hxA⟩
  have hx1 : x ∈ interior (closure (interior (A : Set X))) := (hP2 A hAS) hxA
  have hA_subset : (A : Set X) ⊆ ⋃₀ 𝓢 := by
    intro y hy
    exact Set.mem_sUnion.mpr ⟨A, hAS, hy⟩
  have hsubset_interior : interior (A : Set X) ⊆ interior (⋃₀ 𝓢) :=
    interior_mono hA_subset
  have hsubset :
      closure (interior (A : Set X)) ⊆ closure (interior (⋃₀ 𝓢)) :=
    closure_mono hsubset_interior
  exact (interior_mono hsubset) hx1

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (interior A) := by
  exact Topology.P2_implies_P3 (by
    simpa using (Topology.P2_interior (A := A)))