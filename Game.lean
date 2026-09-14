import Game.Levels.DemoWorld

-- Here's what we'll put on the title screen
Title "L∃∀Ning Into Group Theory"
Introduction
"
# H1 Welcome to L∃∀Ning Into Group Theory!

*An introduction to group theory through Lean.*

In this game, we will create the basic structures that group theory is concerned with, and prove some fundamental lemmas about them.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
