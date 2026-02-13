

theorem isOpen_interior.compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed ((interior A)ᶜ) := by
  simpa using (isOpen_interior : IsOpen (interior A)).isClosed_compl