import Game.Levels.GroupWorld
import Game.Levels.SubgroupWorld

-- Here's what we'll put on the title screen
Title "L∃∀Ning Into Group Theory"
Introduction
"
# Welcome to L∃∀Ning Into Group Theory!

*An introduction to group theory through Lean.*

In this game, we will create the basic structures that group theory is concerned with, and prove some fundamental theorems about them.
"

Info "
*Game version: 1.0*

# Credits
This game was created by Archisha Biswas (Department of Computer Science) under the supervision of Dr Robert Kropholler (Mathematics Institute) under the University of Warwick's Undergraduate Research Support Scheme.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "An introduction to group theory through Lean"
CaptionLong "In this game, you will prove fundamental facts about groups, subgroups, and group homomorphisms."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
