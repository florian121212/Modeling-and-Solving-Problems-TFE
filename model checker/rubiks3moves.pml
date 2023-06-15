/* Rubik's cube, as a Promela model */
/* Rubik's cube 2x2 is define by 6 faces/colors (up:1, front:2, left:3, back:4, right:5, down:6)
	 with on each face, 4 facelets (up-left:1, up-right:2, down-left:3, down-right:4).
	 3 moves are possible (front clockwise:1, left clockwise:2, up clockwise:3)

        |0|1|
	     |2|3|
	 |0|1|0|1|0|1|0|1|
	 |2|3|2|3|2|3|2|3|
	 	  |0|1|
	     |2|3|

	 square at the intersection is the front face */

#define FACES	6
#define SQRS  4

/* the cube is 6 faces with 4 colors */
typedef Face { byte s[SQRS] };
Face cube[FACES];
byte last_move;
byte same_move;

proctype rubiks () {
   byte tmp = 0;
   
   do
   :: assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));
   :: d_step { /* move front clockwise */
	(!(last_move == 1 && same_move == 3)) -> 
	  printf("F ");
	  tmp = cube[1].s[0];
	  cube[1].s[0] = cube[1].s[2];
	  cube[1].s[2] = cube[1].s[3];
	  cube[1].s[3] = cube[1].s[1];
	  cube[1].s[1] = tmp;
	  tmp = cube[0].s[2];
	  cube[0].s[2] = cube[2].s[3];
	  cube[2].s[3] = cube[5].s[1];
	  cube[5].s[1] = cube[4].s[0];
	  cube[4].s[0] = tmp;
	  tmp = cube[0].s[3];
	  cube[0].s[3] = cube[2].s[1];
	  cube[2].s[1] = cube[5].s[0];
	  cube[5].s[0] = cube[4].s[2];
	  cube[4].s[2] = tmp;

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));

     if
	  ::(last_move == 1) -> same_move++
	  :: else -> last_move = 1; same_move = 1
	  fi
	   }
	:: d_step { /* move left clockwise */
	(!(last_move == 2 && same_move == 3)) -> 
	  printf("L ");
	  tmp = cube[2].s[0]
	  cube[2].s[0] = cube[2].s[2]
	  cube[2].s[2] = cube[2].s[3]
	  cube[2].s[3] = cube[2].s[1]
	  cube[2].s[1] = tmp
	  tmp = cube[0].s[0]
	  cube[0].s[0] = cube[3].s[3]
	  cube[3].s[3] = cube[5].s[0]
	  cube[5].s[0] = cube[1].s[0]
	  cube[1].s[0] = tmp
	  tmp = cube[0].s[2]
	  cube[0].s[2] = cube[3].s[1]
	  cube[3].s[1] = cube[5].s[2]
	  cube[5].s[2] = cube[1].s[2]
	  cube[1].s[2] = tmp

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));

	  if
	  ::(last_move == 2) -> same_move++
	  :: else -> last_move = 2; same_move = 1
	  fi
	  	}
	:: d_step { /* move up clockwise */
	(!(last_move == 3 && same_move == 3)) -> 
	  printf("U ");
	  tmp = cube[0].s[0]
	  cube[0].s[0] = cube[0].s[2]
	  cube[0].s[2] = cube[0].s[3]
	  cube[0].s[3] = cube[0].s[1]
	  cube[0].s[1] = tmp
	  tmp = cube[3].s[1]
	  cube[3].s[1] = cube[2].s[1]
	  cube[2].s[1] = cube[1].s[1]
	  cube[1].s[1] = cube[4].s[1]
	  cube[4].s[1] = tmp
	  tmp = cube[3].s[0]
	  cube[3].s[0] = cube[2].s[0]
	  cube[2].s[0] = cube[1].s[0]
	  cube[1].s[0] = cube[4].s[0]
	  cube[4].s[0] = tmp

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));

	  if
	  ::(last_move == 3) -> same_move++
	  :: else -> last_move = 3; same_move = 1
	  fi
      }
   od
}  

init {
 
/* initialize the situation of each face 
   {orange:0; red:1; green:2; blue:3; yellow:4; white:5} */

  last_move = 0;

  cube[0].s[0] = 0;
  cube[0].s[1] = 0; 
  cube[0].s[2] = 0;
  cube[0].s[3] = 0; 

  cube[1].s[0] = 1;
  cube[1].s[1] = 1;
  cube[1].s[2] = 2;
  cube[1].s[3] = 2;

  cube[2].s[0] = 2;
  cube[2].s[1] = 2;
  cube[2].s[2] = 3;
  cube[2].s[3] = 3;

  cube[3].s[0] = 3;
  cube[3].s[1] = 3;
  cube[3].s[2] = 4;
  cube[3].s[3] = 4;

  cube[4].s[0] = 4;
  cube[4].s[1] = 4;
  cube[4].s[2] = 1;
  cube[4].s[3] = 1;

  cube[5].s[0] = 5;
  cube[5].s[1] = 5;
  cube[5].s[2] = 5;
  cube[5].s[3] = 5;

  /* start the simulation */
  run rubiks()
}