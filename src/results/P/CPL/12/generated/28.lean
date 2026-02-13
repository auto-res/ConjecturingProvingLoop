

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hx
  -- `A` is nonempty since it contains `x`.
  have hne : (A : Set X).Nonempty := ⟨x, hx⟩
  -- In a subsingleton every nonempty subset is the whole space.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      rcases hne with ⟨z, hz⟩
      have : y = z := Subsingleton.elim y z
      simpa [this] using hz
  -- Rewrite the goal using `A = univ`; it reduces to `x ∈ univ`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, interior_univ, closure_univ, interior_univ] using this

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  intro x hx
  -- Since `A` is nonempty (as it contains `x`) and the space is a subsingleton,
  -- every point equals `x`, so `A = univ`.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using this equality and conclude.
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, closure_univ, interior_univ] using this