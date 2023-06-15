#########################
#  Rubik's cube solver  #
#########################
use rubiks9moves.pml or rubiks3moves.pml to solve the Rubik's cube respectively 9 or 3 different movements

Tansform code for the model checker in pan.c:
	
	spin -a filename.pml 
		-filename: file with the code

compile c code in an executable file pan:

	gcc pan.c -o pan [-DBFS][-DMEMLIM=...]
		-DBFS (optional): active bread first search, depth first search by default.
		-DMEMLIM=... (optional): for ... Megabytes of memory, 1024Mb by default.

execute model checking:

	pan [-m...]
		-m... (optional): limit depth of the search to ... states. 
			In 2x2 cube with 9 movements, first move is at state 26 -> -m36 allows to check at a depth of 11 moves.
					With 3 movements, first move is at state 27 -> -m59 allows to check at a depth of 33 moves.

see results of the search if finished :

	spin -t filename.pml 
		-filename: file with the code

use: ispin filename.pml for the graphic interface

#########################
#       Solitaire       #
#########################
use solitaire.pml to find a solution to the solitaire (model not enough optimised to work on a normal computer)