

theorem closure_interior_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) (n.succ) A =
      closure (interior A) := by
  -- Define `f := closure ∘ interior`.
  let f : Set X → Set X := fun S => closure (interior S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.closure_interior_idempotent (X := X) (A := S)
  -- Iterating an idempotent function on a fixed point leaves it unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the desired iterate so it starts from the fixed point `f A`.
  have h1 : Nat.iterate f (n.succ) A = Nat.iterate f n (f A) := by
    simp [Nat.iterate]
  -- Since `f A` is fixed, the right-hand side simplifies to `f A`.
  have h2 : Nat.iterate f n (f A) = f A := by
    have hfix : f (f A) = f A := hf_id A
    exact (iterate_fixed hfix) n
  -- Assemble the equalities and unfold `f`.
  have : Nat.iterate f (n.succ) A = f A := by
    simpa [h1, h2]
  simpa [f] using this