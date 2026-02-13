

theorem P1_inter_right_of_open {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → IsOpen (B : Set X) → Topology.P1 (A ∩ B) := by
  classical
  intro hP1A hOpenB
  dsimp [Topology.P1] at hP1A ⊢
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- `x` lies in the closure of `interior A`.
  have hx_clA : x ∈ closure (interior (A : Set X)) := hP1A hxA
  -- We show that `x` also belongs to the closure of `interior A ∩ B`.
  have hx_clAB : x ∈ closure ((interior (A : Set X)) ∩ B) := by
    -- Use the characterisation of closure via neighbourhoods.
    refine (mem_closure_iff).2 ?_
    intro U hUopen hxU
    -- Consider the open neighbourhood `U ∩ B` of `x`.
    have hUBopen : IsOpen (U ∩ B) := hUopen.inter hOpenB
    have hxUB : x ∈ U ∩ B := And.intro hxU hxB
    -- Since `x ∈ closure (interior A)`, the intersection with `interior A` is nonempty.
    have hNonempty :
        ((U ∩ B) ∩ interior (A : Set X)).Nonempty :=
      (mem_closure_iff).1 hx_clA (U ∩ B) hUBopen hxUB
    -- Rearrange the intersection to fit the required shape.
    simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm,
      Set.inter_right_comm] using hNonempty
  -- Because `B` is open, `interior (A ∩ B) = interior A ∩ B`.
  have hInt_eq :
      interior ((A ∩ B) : Set X) = (interior (A : Set X)) ∩ B :=
    interior_inter_right_open (X := X) (A := A) (B := B) hOpenB
  -- Re‐express the previous membership with the identified interior.
  have : x ∈ closure (interior ((A ∩ B) : Set X)) := by
    simpa [hInt_eq] using hx_clAB
  exact this