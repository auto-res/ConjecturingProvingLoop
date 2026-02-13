

theorem P1_subsingleton (X : Type*) [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hx
  -- In a subsingleton space, any nonempty set is the whole space.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Hence `closure (interior A)` is `univ`, so the claim follows.
  have : x ∈ closure (interior A) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hA_univ, interior_univ, closure_univ] using this
  exact this