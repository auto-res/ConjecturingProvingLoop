

theorem interior_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  ext x
  constructor
  · intro hx
    have hsubset : closure (interior (closure A)) ⊆ closure A := by
      have h : (interior (closure A) : Set X) ⊆ closure A := interior_subset
      simpa using (closure_mono h)
    exact (interior_mono hsubset) hx
  · intro hx
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    have hsubset : interior (closure A) ⊆ closure (interior (closure A)) := subset_closure
    have hsub_interior : interior (closure A) ⊆ interior (closure (interior (closure A))) :=
      interior_maximal hsubset h_open
    exact hsub_interior hx