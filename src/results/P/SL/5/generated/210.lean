

theorem interior_closure_iterate_from_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => interior (closure S)) (n.succ) (closure (A : Set X)) =
      interior (closure A) := by
  -- Define `f := interior ∘ closure`.
  let f : Set X → Set X := fun S => interior (closure S)
  -- `f` is idempotent.
  have hf_id : ∀ S : Set X, f (f S) = f S := by
    intro S
    dsimp [f]
    simpa using Topology.interior_closure_idempotent (X := X) (A := S)
  -- Helper: a fixed point remains fixed under any number of iterations.
  have iterate_fixed {S : Set X} (hfix : f S = S) :
      ∀ m : ℕ, Nat.iterate f m S = S := by
    intro m
    induction m with
    | zero => simpa
    | succ m ih => simpa [Nat.iterate, hfix, ih]
  -- Compute `f (closure A)`.
  have hfc : f (closure (A : Set X)) = interior (closure A) := by
    dsimp [f]
    simpa [closure_closure]
  -- `interior (closure A)` is a fixed point of `f`.
  have hfix_int : f (interior (closure A)) = interior (closure A) := by
    dsimp [f]
    simpa using
      Topology.interior_closure_idempotent (X := X) (A := closure A)
  -- Rewrite the desired iterate in terms of the fixed point and simplify.
  calc
    Nat.iterate f (n.succ) (closure (A : Set X))
        = Nat.iterate f n (f (closure (A : Set X))) := by
          simp [Nat.iterate]
    _ = Nat.iterate f n (interior (closure A)) := by
          simpa [hfc]
    _ = interior (closure A) := by
          simpa using (iterate_fixed hfix_int n)