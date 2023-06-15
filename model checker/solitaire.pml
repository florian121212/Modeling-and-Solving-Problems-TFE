/* Solitaire, as a Promela model */
/* Solitaire is defined by a cross composed of five 3x3 squares 
   Each cell contains a ball excepted the cell of the middle of the cross*/

#define size 9

typedef Column { bool c[size] };
Column cross[size];
byte iteration;

proctype r (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}  

proctype d (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype l (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype u (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype dr (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype dl (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype ul (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype ur (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype drl (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype dlu (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype ulr (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype urd (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

proctype urdl (byte x0, y0) {
   byte x = x0;
   byte y = y0;
   
   do
   :: d_step { 
	(cross[x].c[y] == true && cross[x].c[y+1] == true && cross[x].c[y+2] == false) -> 
	  printf("u(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y+1] = false;
	  cross[x].c[y+2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x+1].c[y] == true && cross[x+2].c[y] == false) -> 
	  printf("r(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x+1].c[y] = false;
	  cross[x+2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x].c[y-1] == true && cross[x].c[y-2] == false) -> 
	  printf("d(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x].c[y-1] = false;
	  cross[x].c[y-2] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
	:: d_step { 
	(cross[x].c[y] == true && cross[x-1].c[y] == true && cross[x-2].c[y] == false) -> 
	  printf("l(%d, %d)\n", x, y);
	  cross[x].c[y] = false;
	  cross[x-1].c[y] = false;
	  cross[x-2].c[y] = true;
	  iteration++;
	  assert(!(iteration == 43 && cross[4].c[4] == true))
	  }
   od
}

init {
 
/* initialize the solitaire */

  byte i,j;
  iteration = 0;

  i = 0;
  do
  :: (i < size) ->
        j = 0;
        do
        :: (j < size) -> cross[i].c[j] = true; j++
        :: (j == size) -> break
        od;
        i++
  :: (i == size) -> break
  od;

	cross[4].c[4] = false;

  /* start the simulation */
  run l(7,4);
  run l(8,4);
  run r(0,4);
  run r(1,4);
  run u(4,0);
  run u(4,1);
  run d(4,7);
  run d(4,8);
  run dr(0,5);
  run dr(1,5);
  run dr(3,7);
  run dr(3,8);
  run ur(0,3);
  run ur(1,3);
  run ur(3,0);
  run ur(3,1);
  run dl(5,7);
  run dl(5,8);
  run dl(7,5);
  run dl(8,5);
  run ul(5,0);
  run ul(5,1);
  run ul(7,3);
  run ul(8,3);
  run drl(2,5);
  run drl(6,5);
  run dlu(5,2);
  run dlu(5,6);
  run ulr(2,3);
  run ulr(6,3);
  run urd(3,2);
  run urd(3,6);
  run urdl(2,4);
  run urdl(4,2);
  run urdl(6,4);
  run urdl(4,6);
  run urdl(3,3);
  run urdl(3,4);
  run urdl(3,5);
  run urdl(4,3);
  run urdl(4,4);
  run urdl(4,5);
  run urdl(5,3);
  run urdl(5,4);
  run urdl(5,5)
}