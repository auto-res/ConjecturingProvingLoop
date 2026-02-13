

theorem closure_interior_closure_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior (closure S))) (n.succ) A =
      closure (interior (closure A)) := by
  -- Define the idempotent function `f`.
  let f : Set X → Set X := fun S => closure (interior (closure S))
  -- Show that `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    -- Apply the idempotency lemma to `closure S`.
    simpa using
      Topology.closure_interior_idempotent (X := X) (A := closure S)
  -- A helper lemma: iterating an idempotent function on a fixed point
  -- leaves the point unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the desired iterate so it starts from the fixed point `f A`.
  have h₁ : Nat.iterate f (n.succ) A =
      Nat.iterate f n (f A) := by
    simp [Nat.iterate]
  -- Since `f A` is a fixed point, the right-hand side collapses to `f A`.
  have h₂ : Nat.iterate f n (f A) = f A := by
    have hfix : f (f A) = f A := hf_id A
    exact iterate_fixed hfix n
  -- Assemble the equalities and unfold `f`.
  have : Nat.iterate f (n.succ) A = f A := by
    simpa [h₁, h₂]
  simpa [f] using this