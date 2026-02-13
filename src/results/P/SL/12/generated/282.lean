

theorem IsOpen.compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsOpen (s : Set X)) :
    IsClosed ((s : Set X)ᶜ) := by
  simpa using h.isClosed_compl

theorem IsClosed.compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsClosed (s : Set X)) :
    IsOpen ((s : Set X)ᶜ) := by
  simpa using h.isOpen_compl