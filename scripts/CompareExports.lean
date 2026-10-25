import Main

/-! Replay fresh exports with the pinned comparator's unchanged verification API. -/

#eval do
  let configText ← IO.FS.readFile "comparator.json"
  let configJson ← IO.ofExcept (Lean.Json.parse configText)
  let config : Comparator.Config ← IO.ofExcept (Lean.fromJson? configJson)
  let challenge ← IO.FS.readFile "Challenge.ndjson"
  let solution ← IO.FS.readFile "Solution.ndjson"
  Comparator.M.run (Comparator.verifyMatch challenge solution) config
  IO.println "Comparator.verifyMatch completed successfully"
