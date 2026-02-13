

theorem interior_closure_interior_iterate {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure (interior S))) (n.succ) A =
      interior (closure (interior A)) := by
  -- Define `f := interior ∘ closure ∘ interior`.
  let f : Set X → Set X := fun S => interior (closure (interior S))
  -- Show that `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using
      Topology.interior_closure_idempotent_iter (X := X) (A := S)
  -- A helper lemma: iterating an idempotent function on a fixed point leaves it unchanged.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Rewrite the `(n.succ)`-th iterate starting from `A` so that it starts from the fixed point `f A`.
  have h_step : Nat.iterate f (n.succ) A = Nat.iterate f n (f A) := by
    simp [Nat.iterate]
  -- Since `f A` is a fixed point of `f`, the right-hand side simplifies to `f A`.
  have h_iter : Nat.iterate f n (f A) = f A := by
    have hfix : f (f A) = f A := hf_id A
    exact iterate_fixed hfix n
  -- Assemble the equalities and unfold `f`.
  have : Nat.iterate f (n.succ) A = f A := by
    simpa [h_step, h_iter]
  simpa [f] using this