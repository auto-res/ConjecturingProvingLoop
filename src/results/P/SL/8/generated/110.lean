

theorem isClosed_of_closureInterior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) :
    IsClosed A := by
  have : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using this