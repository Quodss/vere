//  Just a bunch of declarations
//  Ideally these bindings should be generated automatically from header files
//
u3_noun :: #type u32;
c3_c    :: #type u8;
u3_atom :: #type u3_noun;

u3x_sam :: 6;

u3j_cook    :: (key_c: *c3_c, cor: u3_noun, tam_c: *c3_c) -> u3_noun #c_call #foreign;
u3a_gain    :: (a: u3_noun) -> u3_noun #c_call #foreign;
u3n_slam_on :: (gat: u3_noun, sam: u3_noun) -> u3_noun #c_call #foreign;
u3x_good    :: (a: u3_noun) -> u3_noun #c_call #foreign;
u3r_at      :: (a: u3_atom, b: u3_noun) -> u3_noun #c_call #foreign;

u3k :: u3a_gain;
