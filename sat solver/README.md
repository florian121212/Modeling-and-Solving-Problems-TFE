#  snake cube solver  #
use snake_cube.py for the resolution of a cube (same size for each dimension). It uses symmetry clauses

	py snake_cube.py filename.txt selectionstrategy
	-filename is a file name
	-selectionstrategy is a string ("Positive" or "Negative"), nothing if default strategy (RSATPhaseSelectionStrategy)

snake_rectangle.py for the resolution of rectangle (size can be different for each dimension) no symmetry clauses

	py snake_rectangle.py filename.txt xyz selectionstrategy
	
	-filename is a file name
	-xyz are dimension of the block x<=y<=z (e.g 334)
	-selectionstrategy is a string ("Positive" or "Negative"), nothing if default strategy (RSATPhaseSelectionStrategy)

cnffile with remote controller

	java -jar sat4j-sat.jar -remote cnffile

snake_cube_inv.py and snake_rectangle_inv.py work in the same way as snake_cube.py and snake_rectangle.py but instead of having
	constraints: -at most one block per cube cell 
			 -each block at least once
	we have: -each block at most once
		   -at least one block per cube cell

#   rubik's solver    #
use rubiks_sat.py for the resolution of a Rubik's cube 2x2 with one predicate per movement

	py rubik_sat.py filename.txt nb_moves [selectionstrategy]
	-filename is the file with the initial state of the Rubik's cube
	-nb_moves is a non negative integer which is the maximum number of moves to solve the Rubik's cube 
	-selectionstrategy (optional) is a string ("Positive" or "Negative"), nothing if default strategy (RSATPhaseSelectionStrategy)

use rubiks_binary.py for the resolution of a rubik's cube 2x2 with a binary encoding of movements

	py rubik_binary.py filename.txt [selectionstrategy]
	-filename is the file with the initial state of the Rubik's cube
	-selectionstrategy (optional) is a string ("Positive" or "Negative"), nothing if default strategy (RSATPhaseSelectionStrategy)

#   othello solver    #
use othello_sat.py to find a gameplay of othello with a maximum number of moves

	py othello_sat.py size [nb_moves] [selectionstrategy]
	-size is the size of the board
	-nb_moves (optional) is the maximum number of move in the game
	-selectionstrategy (optional) is a string ("Positive" or "Negative"), nothing if default strategy (RSATPhaseSelectionStrategy)
