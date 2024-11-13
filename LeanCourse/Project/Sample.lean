/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/
