#import "u3";

#program_export u3we_mole :: (cor: u3_noun) -> u3_noun #c_call {
    hok := u3j_cook("u3we_mole-mure", u3k(cor), "mure");
    return u3n_slam_on(hok, u3k(u3x_good(u3r_at(u3x_sam, cor))));
}

#program_export u3w_some_complex_function :: (cor: u3_noun) -> u3_noun #c_call {
    //  some uncounted references
    //
    sam := u3x_good(u3r_at(u3x_sam, cor));
    pay := u3x_good(u3r_at(7, cor));
    a := u3x_good(u3r_at(2, sam));
    //  counted references
    //
    b := u3k(u3x_good(u3r_at(6, sam)));
    c := u3k(u3x_good(u3r_at(7, sam)));
    //  refcount violation: conditional loss
    //
    if ( u3_(u3ud(c)) ) {
        u3z(c);
    }
    u3r_sing(sam, pay);
    //  refcount violation: `a` is no longer live due to unifying equality
    //
    if ( u3_(u3du(a)) ) {
        u3r_sing(u3x_good(u3r_at(2, a)), u3x_good(u3r_at(3, a)));
    }
    //  refcount violation: `b` is leaked0
    //
    return u3k(sam);
}
