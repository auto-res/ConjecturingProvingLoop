

theorem Topology.closure_compl_eq_univ_iff_interior_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ : Set X) = Set.univ ↔ interior A = (∅ : Set X) := by
  -- The basic relation between closure of a complement and interior.
  have h_rel := Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  constructor
  · intro h_cl
    -- Rewrite `h_cl` using `h_rel` to get an equality of complements.
    have h_compl : (interior A)ᶜ = (Set.univ : Set X) := by
      simpa [h_rel] using h_cl
    -- Complement both sides to deduce `interior A = ∅`.
    have : interior A = (∅ : Set X) := by
      simpa using congrArg (fun s : Set X => sᶜ) h_compl
    simpa using this
  · intro h_int
    -- Substitute `h_int` into `h_rel` to obtain the desired equality.
    simpa [h_int] using h_rel