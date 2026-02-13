

theorem nonempty_of_closureInterior_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty → A.Nonempty := by
  intro hClInt
  -- First, turn non-emptiness of `closure (interior A)` into non-emptiness of `interior A`.
  have hInt : (interior A).Nonempty :=
    ((closureInterior_nonempty_iff_interior_nonempty (X := X) (A := A)).1 hClInt)
  -- Then use the fact that a non-empty interior forces the original set to be non-empty.
  exact interior_nonempty_imp_nonempty (X := X) (A := A) hInt