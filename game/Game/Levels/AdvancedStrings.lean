import Game.Levels.AdvancedStrings.L01_SuffixAtZero
import Game.Levels.AdvancedStrings.L02_SuffixLengthFormula
import Game.Levels.AdvancedStrings.L03_EmptyTerminalSuffix
import Game.Levels.AdvancedStrings.L04_SuffixIndexCount
import Game.Levels.AdvancedStrings.L05_ValidSuffixPositions
import Game.Levels.AdvancedStrings.L06_SuffixListCount
import Game.Levels.AdvancedStrings.L07_EmptyLCP
import Game.Levels.AdvancedStrings.L08_SelfLCP
import Game.Levels.AdvancedStrings.L09_LexicographicReflexivity
import Game.Levels.AdvancedStrings.L10_SingletonSuffixArray

World "AdvancedStrings"
Title "Advanced Strings"

Introduction "Suffix arrays index every suffix of a text for fast search.
This branch isolates the combinatorics behind that indexing — counting and
bounding suffixes, measuring longest common prefixes, and certifying a
lexicographic ordering — before any heavier construction machinery."
