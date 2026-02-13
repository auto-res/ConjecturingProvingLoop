

theorem P1_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 A) (hAB : A ⊆ B) :
    A ⊆ closure B := by
  dsimp [Topology.P1] at hP1
  intro x hxA
  have hxClA : x ∈ closure (interior A) := hP1 hxA
  have h_cl_subset : closure (interior A) ⊆ closure (interior B) := by
    have h_int : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono h_int
  have hxClIntB : x ∈ closure (interior B) := h_cl_subset hxClA
  have h_final : closure (interior B) ⊆ closure B := by
    have h_intB : interior B ⊆ B := interior_subset
    exact closure_mono h_intB
  exact h_final hxClIntB