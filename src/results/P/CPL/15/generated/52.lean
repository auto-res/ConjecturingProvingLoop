

theorem P2_iteration_fixed {X : Type*} [TopologicalSpace X] {A : Set X} : (Nat.iterate (fun S : Set X => interior (closure (interior S))) 3 A) ⊆ interior (closure (interior A)) := by
  -- Define the operator that is iterated.
  let f : Set X → Set X := fun S : Set X => interior (closure (interior S))

  -- Key lemma: a double application of `f` is contained in a single one.
  have hf_step : ∀ S : Set X, f (f S) ⊆ f S := by
    intro S
    dsimp [f]
    -- 1.  `interior (closure (interior S)) ⊆ closure (interior S)`
    have h₁ :
        (interior (closure (interior S)) : Set X) ⊆
          closure (interior S) :=
      interior_subset
    -- 2.  Take closures on both sides; rewrite `closure (closure _)`.
    have h₂ :
        (closure (interior (closure (interior S))) : Set X) ⊆
          closure (interior S) := by
      have h' :
          (closure (interior (closure (interior S))) : Set X) ⊆
            closure (closure (interior S)) :=
        closure_mono h₁
      simpa [closure_closure] using h'
    -- 3.  Take interiors once more to arrive at the desired inclusion.
    have h₃ :
        (interior (closure (interior (closure (interior S)))) : Set X) ⊆
          interior (closure (interior S)) :=
      interior_mono h₂
    -- The two sides are precisely `f (f S)` and `f S`.
    simpa [f] using h₃

  -- Apply the shrinking lemma twice to control the triple iterate.
  have h₁ : (Nat.iterate f 3 A) ⊆ f (f A) := by
    -- `Nat.iterate f 3 A` is definitionally `f (f (f A))`.
    simpa [Nat.iterate] using hf_step (f A)
  have h₂ : f (f A) ⊆ f A := hf_step A
  have h_final : (Nat.iterate f 3 A) ⊆ f A := h₁.trans h₂

  -- Rewrite `f A` to the required expression and finish.
  simpa [f] using h_final

theorem P2_union_complement {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P2_univ (X := X))

theorem P1_inter_complement {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (A ∩ Aᶜ) := by
  simpa [Set.inter_compl_self] using (P1_empty (X := X))