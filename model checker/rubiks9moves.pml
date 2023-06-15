/* Rubik's cube, as a Promela model */
/* Rubik's cube 2x2 is define by 6 faces/colors (up:0, front:1, left:2, back:3, right:4, down:5)
	 with on each face, 4 squares (up-left:0, up-right:1, down-left:2, down-right:3).
	 9 moves are possible (front clockwise:1, front counterclockwise:2, double front:3,
	 left clockwise:4, left counterclockwise:5, double left:6, up clockwise:7, 
	 up counterclockwise:8, double up:9)

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
	(!(last_move == 1 || last_move == 4 || last_move == 7)) -> 
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
	   
	  last_move = 1;
	   }
	:: d_step { /* move front counterclockwise */
	(!(last_move == 1 || last_move == 4 || last_move == 7)) -> 
	  printf("F' ");
	  tmp = cube[1].s[0];
	  cube[1].s[0] = cube[1].s[1];
	  cube[1].s[1] = cube[1].s[3];
	  cube[1].s[3] = cube[1].s[2];
	  cube[1].s[2] = tmp;
	  tmp = cube[0].s[2];
	  cube[0].s[2] = cube[4].s[0];
	  cube[4].s[0] = cube[5].s[1];
	  cube[5].s[1] = cube[2].s[3];
	  cube[2].s[3] = tmp;
	  tmp = cube[0].s[3];
	  cube[0].s[3] = cube[4].s[2];
	  cube[4].s[2] = cube[5].s[0];
	  cube[5].s[0] = cube[2].s[1];
	  cube[2].s[1] = tmp;

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));

	   last_move = 4;
	   }
	:: d_step { /* move double front */
	(!(last_move == 7 || last_move == 4 || last_move == 1)) -> 
	  printf("F2 ");
	  tmp = cube[1].s[0];
	  cube[1].s[0] = cube[1].s[3];
	  cube[1].s[3] = tmp;
	  tmp = cube[1].s[1];
	  cube[1].s[1] = cube[1].s[2];
	  cube[1].s[2] = tmp;
	  tmp = cube[0].s[2];
	  cube[0].s[2] = cube[5].s[1];
	  cube[5].s[1] = tmp;
	  tmp = cube[0].s[3];
	  cube[0].s[3] = cube[5].s[0];
	  cube[5].s[0] = tmp;
	  tmp = cube[2].s[1];
	  cube[2].s[1] = cube[4].s[2];
	  cube[4].s[2] = tmp;
	  tmp = cube[2].s[3];
	  cube[2].s[3] = cube[4].s[0];
	  cube[4].s[0] = tmp;

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));
	   
	  last_move = 7;
	   }
	:: d_step { /* move left clockwise */
	(!(last_move == 2 || last_move == 5 || last_move == 8)) -> 
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
	  	
	  last_move = 2;
	  	}
	:: d_step { /* move left counterclockwise */
	(!(last_move == 2 || last_move == 5 || last_move == 8)) -> 
	  printf("L' ");
	  tmp = cube[2].s[0]
	  cube[2].s[0] = cube[2].s[1]
	  cube[2].s[1] = cube[2].s[3]
	  cube[2].s[3] = cube[2].s[2]
	  cube[2].s[2] = tmp
	  tmp = cube[0].s[0]
	  cube[0].s[0] = cube[1].s[0]
	  cube[1].s[0] = cube[5].s[0]
	  cube[5].s[0] = cube[3].s[3]
	  cube[3].s[3] = tmp
	  tmp = cube[0].s[2]
	  cube[0].s[2] = cube[1].s[2]
	  cube[1].s[2] = cube[5].s[2]
	  cube[5].s[2] = cube[3].s[1]
	  cube[3].s[1] = tmp

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));

	   last_move = 5;
	  	}
	:: d_step { /* move double left */
	(!(last_move == 2 || last_move == 5 || last_move == 8)) -> 
	  printf("L2 ");
	  tmp = cube[2].s[0];
	  cube[2].s[0] = cube[2].s[3];
	  cube[2].s[3] = tmp;
	  tmp = cube[2].s[1];
	  cube[2].s[1] = cube[2].s[2];
	  cube[2].s[2] = tmp;
	  tmp = cube[1].s[0];
	  cube[1].s[0] = cube[3].s[3];
	  cube[3].s[3] = tmp;
	  tmp = cube[1].s[2];
	  cube[1].s[2] = cube[3].s[1];
	  cube[3].s[1] = tmp;
	  tmp = cube[0].s[0];
	  cube[0].s[0] = cube[5].s[0];
	  cube[5].s[0] = tmp;
	  tmp = cube[0].s[2];
	  cube[0].s[2] = cube[5].s[2];
	  cube[5].s[2] = tmp;

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));
	   
	  last_move = 8;
	   }
	:: d_step { /* move up clockwise */
	(!(last_move == 3 || last_move == 6 || last_move == 9)) -> 
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
      
	  last_move = 3;
      }
   :: d_step { /* move up counterclockwise */
	(!(last_move == 3 || last_move == 6 || last_move == 9)) -> 
	  printf("U' ");
	  tmp = cube[0].s[0]
	  cube[0].s[0] = cube[0].s[1]
	  cube[0].s[1] = cube[0].s[3]
	  cube[0].s[3] = cube[0].s[2]
	  cube[0].s[2] = tmp
	  tmp = cube[3].s[1]
	  cube[3].s[1] = cube[4].s[1]
	  cube[4].s[1] = cube[1].s[1]
	  cube[1].s[1] = cube[2].s[1]
	  cube[2].s[1] = tmp
	  tmp = cube[3].s[0]
	  cube[3].s[0] = cube[4].s[0]
	  cube[4].s[0] = cube[1].s[0]
	  cube[1].s[0] = cube[2].s[0]
	  cube[2].s[0] = tmp

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));
      
      last_move = 6;
      }
   :: d_step { /* move double up */
	(!(last_move == 3 || last_move == 6 || last_move == 9)) -> 
	  printf("U2 ");
	  tmp = cube[0].s[0];
	  cube[0].s[0] = cube[0].s[3];
	  cube[0].s[3] = tmp;
	  tmp = cube[0].s[1];
	  cube[0].s[1] = cube[0].s[2];
	  cube[0].s[2] = tmp;
	  tmp = cube[1].s[0];
	  cube[1].s[0] = cube[3].s[0];
	  cube[3].s[0] = tmp;
	  tmp = cube[1].s[1];
	  cube[1].s[1] = cube[3].s[1];
	  cube[3].s[1] = tmp;
	  tmp = cube[2].s[0];
	  cube[2].s[0] = cube[4].s[0];
	  cube[4].s[0] = tmp;
	  tmp = cube[2].s[1];
	  cube[2].s[1] = cube[4].s[1];
	  cube[4].s[1] = tmp;

	  assert(!(cube[0].s[0] == cube[0].s[1] && cube[0].s[0] == cube[0].s[2] 
	  			&& cube[0].s[0] == cube[0].s[3] && cube[1].s[0] == cube[1].s[1] 
	  			&& cube[1].s[0] == cube[1].s[2] && cube[1].s[0] == cube[1].s[3]
	  		  	&& cube[2].s[0] == cube[2].s[1] && cube[2].s[0] == cube[2].s[2]
	  		  	&& cube[2].s[0] == cube[2].s[3] && cube[3].s[0] == cube[3].s[1] 
	  		  	&& cube[3].s[0] == cube[3].s[2] && cube[3].s[0] == cube[3].s[3]
	  		  	&& cube[4].s[0] == cube[4].s[1] && cube[4].s[0] == cube[4].s[2]
	  		  	&& cube[4].s[0] == cube[4].s[3]));
	   
	  last_move = 9;
	   }
   od
}  

init {
 
/* initialize the situation of each face 
   {orange:0; red:1; green:2; blue:3; yellow:4; white:5} */

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
