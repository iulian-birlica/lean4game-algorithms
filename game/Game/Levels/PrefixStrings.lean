import Game.Levels.PrefixStrings.L01_CommonPrefixBaseCase
import Game.Levels.PrefixStrings.L02_CommonPrefixMatchStep
import Game.Levels.PrefixStrings.L03_PrefixMeasurement
import Game.Levels.PrefixStrings.L04_BorderLengthBound
import Game.Levels.PrefixStrings.L05_PrefixCharacterization
import Game.Levels.PrefixStrings.L06_KMPMatchSoundness
import Game.Levels.PrefixStrings.L07_ZBoxBound
import Game.Levels.PrefixStrings.L08_ZValueFullMatch
import Game.Levels.PrefixStrings.L09_KMPLinearBudget
import Game.Levels.PrefixStrings.L10_TrieEmptyLookup
import Game.Levels.PrefixStrings.L11_TrieInsertCorrectness

World "PrefixStrings"
Title "Prefix Strings"

Introduction "Pattern matching is full of hidden bookkeeping: prefixes,
borders, Z-boxes, and tries. This branch builds the shared common-prefix
measurement underlying both KMP and the Z-algorithm, then uses it to certify
KMP's matches, bound the Z-algorithm's scan, budget a linear KMP pass, and
prove a trie always finds what was inserted into it."
