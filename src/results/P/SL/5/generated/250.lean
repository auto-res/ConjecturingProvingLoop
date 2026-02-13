

theorem closure_interior_iterate_from_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) (n.succ) (closure (A : Set X)) =
      closure (interior (closure (A : Set X))) := by
  -- Define the idempotent map `f := closure ∘ interior`.
  let f : Set X → Set X := fun S => closure (interior S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.closure_interior_idempotent (X := X) (A := S)
  -- A fixed point of an idempotent function remains fixed under iteration.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the desired iterate so that it starts from the fixed point `f (closure A)`.
  have h_step :
      Nat.iterate f (n.succ) (closure (A : Set X)) =
        Nat.iterate f n (f (closure (A : Set X))) := by
    simp [Nat.iterate]
  -- Since `f (closure A)` is a fixed point, the right‐hand side collapses.
  have h_iter :
      Nat.iterate f n (f (closure (A : Set X))) = f (closure (A : Set X)) := by
    have hfix : f (f (closure (A : Set X))) = f (closure (A : Set X)) := by
      simpa using hf_id (closure (A : Set X))
    exact iterate_fixed hfix n
  -- Assemble the pieces and unfold `f`.
  simpa [h_step, h_iter, f]