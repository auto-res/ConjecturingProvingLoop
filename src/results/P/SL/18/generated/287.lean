

theorem IsOpen.diff {α : Type*} [TopologicalSpace α] {U V : Set α}
    (hU : IsOpen (U : Set α)) (hV : IsClosed (V : Set α)) :
    IsOpen (U \ V : Set α) := by
  have hOpenComplV : IsOpen (Vᶜ : Set α) := by
    simpa using hV.isOpen_compl
  simpa [Set.diff_eq] using hU.inter hOpenComplV