

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P3 A → P3 B → P3 (A ∪ B) := by
  intro hA hB
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ interior (closure A)`
      have hxIntClA : x ∈ interior (closure (A : Set X)) := hA hxA
      -- show this set is contained in the required one
      have h_subset :
          interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) := by
        -- step 1: `A ⊆ A ∪ B`
        have h_set : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        -- step 2: take closures
        have h_closure : closure (A : Set X) ⊆ closure (A ∪ B) :=
          closure_mono h_set
        -- step 3: take interiors
        exact interior_mono h_closure
      exact h_subset hxIntClA
  | inr hxB =>
      -- `x ∈ interior (closure B)`
      have hxIntClB : x ∈ interior (closure (B : Set X)) := hB hxB
      -- analogous inclusion for `B`
      have h_subset :
          interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) := by
        have h_set : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        have h_closure : closure (B : Set X) ⊆ closure (A ∪ B) :=
          closure_mono h_set
        exact interior_mono h_closure
      exact h_subset hxIntClB

theorem closure_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior (closure (interior A))) ⊆ closure A := by
  -- First, prove `interior (closure (interior A)) ⊆ closure A`
  have h :
      interior (closure (interior A)) ⊆ closure (A : Set X) := by
    calc
      interior (closure (interior A))
          ⊆ closure (interior A) := interior_subset
      _ ⊆ closure A := by
        exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Then take closures of both sides and use `closure_closure`
  simpa [closure_closure] using (closure_mono h)