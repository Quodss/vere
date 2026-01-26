//  Just a bunch of declarations
//  Ideally these bindings should be generated automatically from header files
//
u3_noun :: #type u32;
c3_c    :: #type u8;
c3_o    :: enum u8 {
    c3y :: 0;
    c3n :: 1;
}
u3_atom :: #type u3_noun;

u3x_sam :: 6;

u3j_cook    :: (key_c: *c3_c, cor: u3_noun, tam_c: *c3_c) -> u3_noun #c_call #foreign;
u3a_gain    :: (a: u3_noun) -> u3_noun #c_call #foreign;
u3a_lose    :: (a: u3_noun) -> () #c_call #foreign;
u3n_slam_on :: (gat: u3_noun, sam: u3_noun) -> u3_noun #c_call #foreign;
u3x_good    :: (a: u3_noun) -> u3_noun #c_call #foreign;
u3r_at      :: (a: u3_atom, b: u3_noun) -> u3_noun #c_call #foreign;
u3r_sing    :: (a: u3_atom, b: u3_noun) -> c3_o #c_call #foreign;

u3k :: u3a_gain;
u3z :: u3a_lose;


not :: (a: c3_o) -> c3_o #c_call
{
    return ifx .c3y == a then .c3n else .c3y;
}

u3a_is_cell :: inline (som: u3_noun) -> c3_o #c_call
{
    return ifx 0b11 == som >> 30 then .c3y else .c3n;
}

u3a_is_atom :: inline (som: u3_noun) -> c3_o #c_call
{
    return not(u3a_is_cell(som));
}

u3a_is_cat :: inline (som: u3_noun) -> c3_o #c_call
{
    return ifx som >> 31 then .c3n else .c3y;
}

u3ud :: u3a_is_atom;
u3du :: u3a_is_cell;

u3_ :: (som: c3_o) -> bool #expand {
    return .c3y == som;
}

u3__ :: (x: bool) -> c3_o #expand {
    return ifx x then .c3y else .c3n;
}