

theorem Topology.frontier_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier ((A ∩ B) : Set X) ⊆ frontier (A : Set X) ∪ frontier (B : Set X) := by
  classical
  intro x hx
  -- `hx` states that `x` is in the frontier of `A ∩ B`.
  rcases hx with ⟨hClAB, hNotIntAB⟩
  -- A point in the closure of `A ∩ B` lies in the closures of both `A` and `B`.
  have hClSubset :
      closure ((A ∩ B) : Set X) ⊆
        closure (A : Set X) ∩ closure (B : Set X) :=
    Topology.closure_inter_subset_inter_closure (A := A) (B := B)
  have hClA : x ∈ closure (A : Set X) := (hClSubset hClAB).1
  have hClB : x ∈ closure (B : Set X) := (hClSubset hClAB).2
  -- Case distinction on membership of `x` in the interiors of `A` and `B`.
  by_cases hIntA : x ∈ interior (A : Set X)
  · by_cases hIntB : x ∈ interior (B : Set X)
    · -- If `x` is in both interiors, it is in the interior of `A ∩ B`,
      -- contradicting `hNotIntAB`.
      have hInInter :
          x ∈ interior (A : Set X) ∩ interior (B : Set X) :=
        And.intro hIntA hIntB
      have hIntAB : x ∈ interior ((A ∩ B) : Set X) :=
        (interior_inter_subset (A := A) (B := B)) hInInter
      exact (hNotIntAB hIntAB).elim
    · -- `x` is not in `interior B`, hence in the frontier of `B`.
      have hFrontB : x ∈ frontier (B : Set X) := And.intro hClB hIntB
      exact Or.inr hFrontB
  · -- `x` is not in `interior A`; similar reasoning yields membership
    -- in the frontier of `A` or `B`.
    by_cases hIntB : x ∈ interior (B : Set X)
    · -- `x` is not in `interior A` but is in `interior B`, so it belongs
      -- to the frontier of `A`.
      have hFrontA : x ∈ frontier (A : Set X) := And.intro hClA hIntA
      exact Or.inl hFrontA
    · -- `x` is in neither interior; choose either frontier (here, of `A`).
      have hFrontA : x ∈ frontier (A : Set X) := And.intro hClA hIntA
      exact Or.inl hFrontA