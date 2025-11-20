import LeanProofs.Lib
import LeanProofs.Sorted
def sorted_proof : sorted := by
  unfold sorted
  intros
  grind
