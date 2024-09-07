use core::time;
use std::collections::HashMap;
use std::i32;
use std::time::{SystemTime, UNIX_EPOCH};
use std::io::{self, Write};
use regex::Regex;


#[derive(Debug)]
enum Error {
    ZeroBitError,
    IllegalMoveError,
}


// Define bitboard type
type BitBoard = u64;

// Board squares
#[repr(u64)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
enum BoardSquare {
    a8=56, b8=57, c8=58, d8=59, e8=60, f8=61, g8=62, h8=63, no_sq=64,
    a7=48, b7=49, c7=50, d7=51, e7=52, f7=53, g7=54, h7=55,
    a6=40, b6=41, c6=42, d6=43, e6=44, f6=45, g6=46, h6=47,
    a5=32, b5=33, c5=34, d5=35, e5=36, f5=37, g5=38, h5=39,
    a4=24, b4=25, c4=26, d4=27, e4=28, f4=29, g4=30, h4=31,
    a3=16, b3=17, c3=18, d3=19, e3=20, f3=21, g3=22, h3=23,
    a2=8, b2=9, c2=10, d2=11, e2=12, f2=13, g2=14, h2=15,
    a1=0, b1=1, c1=2, d1=3, e1=4, f1=5, g1=6, h1=7,
}

#[repr(u64)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
enum Piece {
    P,
    N,
    B,
    R,
    Q,
    K,
    p,
    n,
    b,
    r,
    q,
    k,
}

#[repr(u64)]
#[allow(dead_code)]
#[derive(PartialEq)]
enum PieceColor {
    WHITE,
    BLACK,
    BOTH
}

#[repr(u64)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
enum Castle {
    wk = 1,
    wq = 2,
    bk = 4,
    bq = 8,
}

#[repr(u64)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
#[derive(PartialEq)]
enum MOVE_TYPE {
    all_moves,
    only_captures
}

static ASCII_PIECES: [&str; 12] = ["P", "N", "B", "R", "Q", "K", "p", "n", "b", "r", "q", "k"];

static UNICODE_PIECES: [&str; 12] = ["♟︎", "♞", "♝", "♜", "♛", "♚","♙", "♘", "♗", "♖", "♕", "♔"];

// piece bitboards
static mut PIECE_BITBOARDS: [BitBoard; 12] = [0; 12];

// occupancy bitboards
static mut OCCUPANCIES: [BitBoard; 3] = [0; 3];

// side to move
static mut SIDE: i32 = 0;

// enpassant square
static mut ENPASSANT: u32 = BoardSquare::no_sq as u32; 

// Castling rights
static mut CASTLE: u32 = 0;

// half move (ply)
static mut PLY: usize = 0;

// best move so far
static mut BEST_MOVE: u64 = 0; 

// NODES searched in a given position

static mut NODES: usize = 0;


// FEN dedug positions
static EMPTY_BOARD: &str = "8/8/8/8/8/8/8/8 w - - ";
static START_POSTITION: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1 ";
static TRICKY_POSITION: &str = "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1 ";
static KILLER_POSITION: &str = "rnbqkb1r/pp1p1pPp/8/2p1pP2/1P1P4/3P3P/P1P1P3/RNBQKBNR w KQkq e6 0 1";
static CMK_POSITION: &str = "r2q1rk1/ppp2ppp/2n1bn2/2b1p3/3pP3/3P1NPP/PPP1NPB1/R1BQ1RK1 b - - 0 9 ";


static MATERIAL_SCORE: [i32; 12] = [
    100,      // white pawn score
    300,      // white knight scrore
    350,      // white bishop score
    500,      // white rook score
   1000,      // white queen score
  10000,      // white king score
   -100,      // black pawn score
   -300,      // black knight scrore
   -350,      // black bishop score
   -500,      // black rook score
  -1000,      // black queen score
 -10000,      // black king score
];


// pawn positional score
static PAWN_SCORE: [i32; 64] = [
    0,   0,   0,   0,   0,   0,   0,   0,
    0,   0,   0, -10, -10,   0,   0,   0,
    0,   0,   0,   5,   5,   0,   0,   0,
    5,   5,  10,  20,  20,   5,   5,   5,
    10,  10,  10,  20,  20,  10,  10,  10,
    20,  20,  20,  30,  30,  30,  20,  20,
    30,  30,  30,  40,  40,  30,  30,  30,
    90,  90,  90,  90,  90,  90,  90,  90,
];

// knight positional score
static KNIGHT_SCORE: [i32; 64] = [
    -5, -10,   0,   0,   0,   0, -10,  -5,
    -5,   0,   0,   0,   0,   0,   0,  -5,
    -5,   5,  20,  10,  10,  20,   5,  -5,
    -5,  10,  20,  30,  30,  20,  10,  -5,
    -5,  10,  20,  30,  30,  20,  10,  -5,
    -5,   5,  20,  20,  20,  20,   5,  -5,
    -5,   0,   0,  10,  10,   0,   0,  -5,
    -5,   0,   0,   0,   0,   0,   0,  -5,
];

// bishop positional score
static  BISHOP_SCORE: [i32; 64] = [
    0,   0, -10,   0,   0, -10,   0,   0,
    0,  30,   0,   0,   0,   0,  30,   0,
    0,  10,   0,   0,   0,   0,  10,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    0,   0,   0,  10,  10,   0,   0,   0,
    0,   0,   0,   0,   0,   0,   0,   0,
    0,   0,   0,   0,   0,   0,   0,   0,
];

// rook positional score
static  ROOK_SCORE: [i32; 64] = [
    0,   0,   0,  20,  20,   0,   0,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    0,   0,  10,  20,  20,  10,   0,   0,
    50,  50,  50,  50,  50,  50,  50,  50,
    50,  50,  50,  50,  50,  50,  50,  50,
];

// king positional score
static  KING_SCORE: [i32; 64] = [
    0,   0,   5,   0, -15,   0,  10,   0,
    0,   5,   5,  -5,  -5,   0,   5,   0,
    0,   0,   5,  10,  10,   5,   0,   0,
    0,   5,  10,  20,  20,  10,   5,   0,
    0,   5,  10,  20,  20,  10,   5,   0,
    0,   5,   5,  10,  10,   5,   5,   0,
    0,   0,   5,   5,   5,   5,   0,   0,
    0,   0,   0,   0,   0,   0,   0,   0,
];

static MIRROR_SCORE: [usize; 64] = [
    63, 62, 61, 60, 59, 58, 57, 56,
    55, 54, 53, 52, 51, 50, 49, 48,
    47, 46, 45, 44, 43, 42, 41, 40,
    39, 38, 37, 36, 35, 34, 33, 32,
    31, 30, 29, 28, 27, 26, 25, 24,
    23, 22, 21, 20, 19, 18, 17, 16,
    15, 14, 13, 12, 11, 10, 9,  8, 
    0 , 1 , 2,  3,  4,  5,  6,  7
];

// most valuable victim & less valuable attacker

/*
                          
    (Victims) Pawn Knight Bishop   Rook  Queen   King
  (Attackers)
        Pawn   105    205    305    405    505    605
      Knight   104    204    304    404    504    604
      Bishop   103    203    303    403    503    603
        Rook   102    202    302    402    502    602
       Queen   101    201    301    401    501    601
        King   100    200    300    400    500    600

*/

static MVV_LVA: [[usize; 12]; 12] = [
    [
        105, 205, 305, 405, 505, 605,  105, 205, 305, 405, 505, 605,
    ],
    [
        104, 204, 304, 404, 504, 604,  104, 204, 304, 404, 504, 604,
    ],
    [
        103, 203, 303, 403, 503, 603,  103, 203, 303, 403, 503, 603,
    ],
    [
        102, 202, 302, 402, 502, 602,  102, 202, 302, 402, 502, 602,
    ],
    [
        101, 201, 301, 401, 501, 601,  101, 201, 301, 401, 501, 601,
    ],
    [
        100, 200, 300, 400, 500, 600,  100, 200, 300, 400, 500, 600,
    ], 

    [
        105, 205, 305, 405, 505, 605,  105, 205, 305, 405, 505, 605,
    ],
    [
        104, 204, 304, 404, 504, 604,  104, 204, 304, 404, 504, 604,
    ],
    [
        103, 203, 303, 403, 503, 603,  103, 203, 303, 403, 503, 603,
    ],
    [
        102, 202, 302, 402, 502, 602,  102, 202, 302, 402, 502, 602,
    ],
    [
        101, 201, 301, 401, 501, 601,  101, 201, 301, 401, 501, 601,
    ],
    [
        100, 200, 300, 400, 500, 600,  100, 200, 300, 400, 500, 600,
    ], 
];

// Killer & History moves

// killer moves [id][ply]
static mut KILLER_MOVES: [[usize; 64];2] = [[0; 64]; 2];
// history moves [piece][square]
static mut HISTORY_MOVES: [[usize; 64];12] = [[0; 64]; 12];

/*
      ================================
            Triangular PV table
      --------------------------------
        PV line: e2e4 e7e5 g1f3 b8c6
      ================================

           0    1    2    3    4    5
      
      0    m1   m2   m3   m4   m5   m6
      
      1    0    m2   m3   m4   m5   m6 
      
      2    0    0    m3   m4   m5   m6
      
      3    0    0    0    m4   m5   m6
       
      4    0    0    0    0    m5   m6
      
      5    0    0    0    0    0    m6
*/

// PV length
static mut PV_LENGTH: [u64; 64] = [0; 64];

// PV table
static mut PV_TABLE: [[u64; 64]; 64] = [[0; 64]; 64];

static mut FOLLOW_PV: u64 = 0;

static mut SCORE_PV: u64 = 0;

// Late move reduction constants

static FULL_DEPTH_MOVE: usize = 4;
static REDUCTION_LIMIT: usize = 3;

/**********************************\
 ==================================
 
       Time controls variables
 
 ==================================
\**********************************/
// exit from engine flag
static mut QUIT: u64 = 0;
// UCI "movestogo" command moves counter
static mut MOVESTOGO: u64 = 30;
// UCI "movetime" command time counter
static mut MOVETIME: i64 = -1;
// UCI "time" command holder (ms)
static mut TIME: i64 = -1;
// UCI "inc" command's time increment holder
static mut INC: i64 = 0;
// UCI "starttime" command time holder
static mut STARTTIME: u64 = 0;
// UCI "stoptime" command time holder
static mut STOPTIME: u64 = 0;
// variable to flag time control availability
static mut TIMESET: u64 = 0;
// variable to flag when the time is up
static mut STOPPED: u64 = 0;



// set/get/reset bit macros
#[macro_export]
macro_rules! get_bit {
    ($bitboard: expr, $square: expr) => {
        if ($bitboard & (1 << $square)) !=0  {
            1
        }else{
            0
        }
    };
}

#[macro_export]
macro_rules! set_bit {
    ($bitboard: expr, $square: expr) => {
        $bitboard |= (1 as u64) << ($square as u64);
    };
}

#[macro_export]
macro_rules! reset_bit {
    ($bitboard: expr, $square: expr) => {
        if get_bit!($bitboard, ($square as u64)) == 1 {
            $bitboard ^= (1 as u64) << ($square as u64);
        }
    };
}

/*
          binary move bits                               hexidecimal constants
    
    0000 0000 0000 0000 0011 1111    source square       0x3f
    0000 0000 0000 1111 1100 0000    target square       0xfc0
    0000 0000 1111 0000 0000 0000    piece               0xf000
    0000 1111 0000 0000 0000 0000    promoted piece      0xf0000
    0001 0000 0000 0000 0000 0000    capture flag        0x100000
    0010 0000 0000 0000 0000 0000    double push flag    0x200000
    0100 0000 0000 0000 0000 0000    enpassant flag      0x400000
    1000 0000 0000 0000 0000 0000    castling flag       0x800000
*/

// encode move
#[macro_export]
macro_rules! encode_move {
    ($source: expr, $target: expr, $piece: expr, $promoted: expr, $capture: expr, $double: expr, $enpassant: expr, $castling: expr) => {
        ($source) | ($target << 6) | ($piece << 12) | ($promoted << 16) | ($capture << 20) | ($double << 21) | ($enpassant << 22) | ($castling << 23)
    };
}

// extract source square
#[macro_export]
macro_rules! get_move_source {
    ($move: expr) => {
        $move & 0x3f
    };
}

// extract target square
#[macro_export]
macro_rules! get_move_target {
    ($move: expr) => {
        ($move & 0xfc0) >> 6
    };
}

// extract piece
macro_rules! get_move_piece {
    ($move: expr) => {
        ($move & 0xf000) >> 12
    };
}

// extract promoted piece
macro_rules! get_move_promoted {
    ($move: expr) => {
        ($move & 0xf0000) >> 16
    };
}

// extract capture flag
macro_rules! get_move_capture {
    ($move: expr) => {
        $move & 0x100000
    };
}

// extract double pawn push flag
macro_rules! get_move_double {
    ($move: expr) => {
        $move & 0x200000
    };
}

// extract castling flag
macro_rules! get_move_enpassant {
    ($move: expr) => {
        $move & 0x400000
    };
}

// extract enpassant flag
macro_rules! get_move_castling {
    ($move: expr) => {
        $move & 0x800000
    };
}


// Random numbers
static mut RANDOM_SEED: u32 = 1804289383;

fn get_random_u32_number() -> u32{
    unsafe {
        // get current state
        let mut number = RANDOM_SEED;
        // XOR shift algorithm
        number ^= number << 13;
        number ^= number >> 17;
        number ^= number << 5;
        // update random number state
        RANDOM_SEED = number;
        number
    }  
}

#[cfg(unix)]
fn input_waiting() -> bool {
    use libc::{poll, pollfd, POLLIN};
    use std::os::unix::io::AsRawFd;

    let stdin_fd = io::stdin().as_raw_fd();
    let mut fds = [pollfd {
        fd: stdin_fd,
        events: POLLIN,
        revents: 0,
    }];

    let timeout = 0; // Non-blocking, immediate return
    let res = unsafe { poll(fds.as_mut_ptr(), fds.len() as u64, timeout) };

    res > 0 && (fds[0].revents & POLLIN) != 0
}

#[cfg(windows)]
fn input_waiting() -> bool {
    use winapi::um::consoleapi::GetNumberOfConsoleInputEvents;
    use winapi::um::processenv::GetStdHandle;
    use winapi::um::winbase::STD_INPUT_HANDLE;
    use winapi::um::winnt::HANDLE;

    unsafe {
        let handle: HANDLE = GetStdHandle(STD_INPUT_HANDLE);
        let mut events: u32 = 0;
        let result = GetNumberOfConsoleInputEvents(handle, &mut events);

        if result == 0 {
            // An error occurred
            false
        } else {
            // If there are more than 1 event, input is available
            events > 1
        }
    }
}


// read GUI/user input
fn read_input() {
    let mut in_buffer = String::new();

    if input_waiting() {
        unsafe{
            STOPPED = 1;
        }

        io::stdin().read_line(&mut in_buffer).expect("failed to read line");
        in_buffer = in_buffer.trim().to_string();

        if in_buffer.len() > 0 {
            if in_buffer.chars().take(4).collect::<Vec<char>>().iter().collect::<String>() == "quit"{
                unsafe {
                    //in_buffer.clear();
                    QUIT = 1;
                }
            }else if in_buffer.chars().take(4).collect::<Vec<char>>().iter().collect::<String>() == "stop" {
                unsafe {
                    //in_buffer.clear();
                    QUIT = 1;
                }
            }
        }

        
    }
}

// a bridge function to interact between search and GUI input
fn communicate() {
    // if time is up break here
    unsafe {
        if TIMESET == 1 && get_time_ms() > STOPTIME {
            STOPPED = 1;
        }
    }

    read_input();
}

fn get_random_u64_number() -> u64 {

    let n1: u64 = u64::from(get_random_u32_number()) & 0xFFFF;
    let n2: u64 = u64::from(get_random_u32_number()) & 0xFFFF;
    let n3: u64 = u64::from(get_random_u32_number()) & 0xFFFF;
    let n4: u64 = u64::from(get_random_u32_number()) & 0xFFFF;

    n1 | (n2 << 16) | (n3 << 32) | (n4 << 48)

}

fn generate_magic_number() -> u64 {
    get_random_u64_number() & get_random_u64_number() & get_random_u64_number()
}

// Magic Number 
fn find_magic_number(square: u64, relevant_bits: u32, bishop_flag: u8) -> u64 {
    // init occupancy
    let mut occupancies: [u64; 4096] = [0; 4096]; 

    // init attack tables
    let mut attacks: [u64; 4096] = [0; 4096]; 

    // init attack mask for current piece
    let attack_mask: u64 = match bishop_flag {
        0 => mask_rook_attacks(square as u64),
        1 => mask_bishop_attacks(square as u64),
        _ => panic!()
    };


    // init occupancy indices
    let occupancy_indices: u32 = 1u32 << relevant_bits;

    // loop over occupancy indices
    for index in 0..occupancy_indices {
        // init occupancies
        occupancies[index as usize] = set_occupancy(index as usize, relevant_bits as usize, attack_mask);

        // init attacks
        if bishop_flag == 1 {
            attacks[index as usize] = bishop_attacks(square as u64, occupancies[index as usize]);
        }else {
            attacks[index as usize] = rook_attacks(square as u64, occupancies[index as usize]);
        }
    }

    // test magic number 
    for _ in 0..100000000{
        // generate magic number candidate
        let magic_number = generate_magic_number();

        // skip invalid magic numbers
        if count_bits((attack_mask.wrapping_mul(magic_number)) & 0xFF00000000000000) < 6 {
            continue;
        }

        // init used attacks
        let mut used_attacks: [u64; 4096] = [0; 4096]; 

        // init index & fail flag
        let mut index: usize = 0;
        let mut fail: bool = false;

        while !fail && (index < (occupancy_indices as usize)){
            // init magic index
            let magic_index = ((occupancies[index].wrapping_mul(magic_number)) >> (64 - relevant_bits)) as u32;

            // test candidate magic index
            if used_attacks[magic_index as usize] == 0 {
                // magic index works
                used_attacks[magic_index as usize] = attacks[index as usize];
            }else if used_attacks[magic_index as usize] != attacks[index as usize] {
                // magic index doesn't work
                fail = true;
            }
            index += 1;

        }

        if !fail {
            return magic_number;
        }

    }

    return  0;
}

fn init_magic_numbers() {
    for square in 0..64 {
        unsafe {
            ROOK_MAGIC_NUMBERS[square as usize] = find_magic_number(square, ROOK_RELEVANT_BITS[square as usize] as u32, 0);
        }
        
    }

    for square in 0..64 {
        unsafe {
            BISHOP_MAGIC_NUMBERS[square as usize] = find_magic_number(square, BISHOP_RELEVANT_BITS[square as usize] as u32, 1);
        }
    }
}

// File masks
static NOT_A_FILE: BitBoard = 18374403900871474942;
/*
 8   0  1  1  1  1  1  1  1
 7   0  1  1  1  1  1  1  1
 6   0  1  1  1  1  1  1  1
 5   0  1  1  1  1  1  1  1
 4   0  1  1  1  1  1  1  1
 3   0  1  1  1  1  1  1  1
 2   0  1  1  1  1  1  1  1
 1   0  1  1  1  1  1  1  1

     a  b  c  d  e  f  g  h
 */

 static NOT_H_FILE: BitBoard = 9187201950435737471;
/*
 8   1  1  1  1  1  1  1  0
 7   1  1  1  1  1  1  1  0
 6   1  1  1  1  1  1  1  0
 5   1  1  1  1  1  1  1  0
 4   1  1  1  1  1  1  1  0
 3   1  1  1  1  1  1  1  0
 2   1  1  1  1  1  1  1  0
 1   1  1  1  1  1  1  1  0

     a  b  c  d  e  f  g  h
 */

 static NOT_HG_FILE: BitBoard = 4557430888798830399;
/*
 8   1  1  1  1  1  1  0  0
 7   1  1  1  1  1  1  0  0
 6   1  1  1  1  1  1  0  0
 5   1  1  1  1  1  1  0  0
 4   1  1  1  1  1  1  0  0
 3   1  1  1  1  1  1  0  0
 2   1  1  1  1  1  1  0  0
 1   1  1  1  1  1  1  0  0

     a  b  c  d  e  f  g  h
 */
 static NOT_AB_FILE: BitBoard = 18229723555195321596;
/*
 8   0  0  1  1  1  1  1  1
 7   0  0  1  1  1  1  1  1
 6   0  0  1  1  1  1  1  1
 5   0  0  1  1  1  1  1  1
 4   0  0  1  1  1  1  1  1
 3   0  0  1  1  1  1  1  1
 2   0  0  1  1  1  1  1  1
 1   0  0  1  1  1  1  1  1

     a  b  c  d  e  f  g  h
 */

// Pawn attacks table [side][square]
static mut PAWN_ATTACKS: [[u64; 64]; 2] = [[0; 64]; 2];

// Knight attacks table [square]
static mut KNIGHT_ATTACKS : [u64; 64] = [0; 64];

// King attacks table [square]
static mut KING_ATTACKS : [u64; 64] = [0; 64];

// bishop attack masks
static mut BISHOP_MASKS: [u64; 64] = [0; 64];

// rook attack masks
static mut ROOK_MASKS: [u64; 64] = [0; 64];

// bishop attacks table [square][occupancy]
static mut BISHOP_ATTACKS: [[u64; 512]; 64] = [[0; 512]; 64];

// rook attacks table [square][occupancy]
static mut ROOK_ATTACKS: [[u64; 4096]; 64] = [[0; 4096]; 64];


static SQUARE_TO_COORD: [&str; 64] = [
    "a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1",
    "a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
    "a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3",
    "a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4",
    "a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
    "a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6",
    "a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7",
    "a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8"
];

// Bishop relevant occupancy bit count for every square on board 
static BISHOP_RELEVANT_BITS: [u8; 64] = [
    6, 5, 5, 5, 5, 5, 5, 6, 
    5, 5, 5, 5, 5, 5, 5, 5, 
    5, 5, 7, 7, 7, 7, 5, 5, 
    5, 5, 7, 9, 9, 7, 5, 5, 
    5, 5, 7, 9, 9, 7, 5, 5, 
    5, 5, 7, 7, 7, 7, 5, 5, 
    5, 5, 5, 5, 5, 5, 5, 5, 
    6, 5, 5, 5, 5, 5, 5, 6
];

// Rook relevant occupancy bit count for every square on board 
static ROOK_RELEVANT_BITS: [u8; 64] = [
    12, 11, 11, 11, 11, 11, 11, 12,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	11, 10, 10, 10, 10, 10, 10, 11,
	12, 11, 11, 11, 11, 11, 11, 12
];


/*

 king & rooks didn't move:     1111 & 1111  =  1111    15

        white king  moved:     1111 & 1100  =  1100    12
  white king's rook moved:     1111 & 1110  =  1110    14
 white queen's rook moved:     1111 & 1101  =  1101    13
     
         black king moved:     1111 & 0011  =  1011    3
  black king's rook moved:     1111 & 1011  =  1011    11
 black queen's rook moved:     1111 & 0111  =  0111    7

*/
// 7, 15, 15, 15,  3, 15, 15, 11,
// Castling rights update constants
static CASTLING_RIGHTS: [u32; 64] = [
    13, 15, 15, 15, 12, 15, 15, 14,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15,
    7, 15, 15, 15,  3, 15, 15, 11
];


// static mut BISHOP_MAGIC_NUMBERS: [u64; 64] = [0; 64];
// bishop magic numbers
static mut BISHOP_MAGIC_NUMBERS: [u64; 64] = [
    0x40040844404084,
    0x2004208a004208,
    0x10190041080202,
    0x108060845042010,
    0x581104180800210,
    0x2112080446200010,
    0x1080820820060210,
    0x3c0808410220200,
    0x4050404440404,
    0x21001420088,
    0x24d0080801082102,
    0x1020a0a020400,
    0x40308200402,
    0x4011002100800,
    0x401484104104005,
    0x801010402020200,
    0x400210c3880100,
    0x404022024108200,
    0x810018200204102,
    0x4002801a02003,
    0x85040820080400,
    0x810102c808880400,
    0xe900410884800,
    0x8002020480840102,
    0x220200865090201,
    0x2010100a02021202,
    0x152048408022401,
    0x20080002081110,
    0x4001001021004000,
    0x800040400a011002,
    0xe4004081011002,
    0x1c004001012080,
    0x8004200962a00220,
    0x8422100208500202,
    0x2000402200300c08,
    0x8646020080080080,
    0x80020a0200100808,
    0x2010004880111000,
    0x623000a080011400,
    0x42008c0340209202,
    0x209188240001000,
    0x400408a884001800,
    0x110400a6080400,
    0x1840060a44020800,
    0x90080104000041,
    0x201011000808101,
    0x1a2208080504f080,
    0x8012020600211212,
    0x500861011240000,
    0x180806108200800,
    0x4000020e01040044,
    0x300000261044000a,
    0x802241102020002,
    0x20906061210001,
    0x5a84841004010310,
    0x4010801011c04,
    0xa010109502200,
    0x4a02012000,
    0x500201010098b028,
    0x8040002811040900,
    0x28000010020204,
    0x6000020202d0240,
    0x8918844842082200,
    0x4010011029020020
];

//static mut ROOK_MAGIC_NUMBERS: [u64; 64] = [0; 64];
// rook magic numbers
static mut ROOK_MAGIC_NUMBERS: [u64; 64] = [
    0x8a80104000800020,
    0x140002000100040,
    0x2801880a0017001,
    0x100081001000420,
    0x200020010080420,
    0x3001c0002010008,
    0x8480008002000100,
    0x2080088004402900,
    0x800098204000,
    0x2024401000200040,
    0x100802000801000,
    0x120800800801000,
    0x208808088000400,
    0x2802200800400,
    0x2200800100020080,
    0x801000060821100,
    0x80044006422000,
    0x100808020004000,
    0x12108a0010204200,
    0x140848010000802,
    0x481828014002800,
    0x8094004002004100,
    0x4010040010010802,
    0x20008806104,
    0x100400080208000,
    0x2040002120081000,
    0x21200680100081,
    0x20100080080080,
    0x2000a00200410,
    0x20080800400,
    0x80088400100102,
    0x80004600042881,
    0x4040008040800020,
    0x440003000200801,
    0x4200011004500,
    0x188020010100100,
    0x14800401802800,
    0x2080040080800200,
    0x124080204001001,
    0x200046502000484,
    0x480400080088020,
    0x1000422010034000,
    0x30200100110040,
    0x100021010009,
    0x2002080100110004,
    0x202008004008002,
    0x20020004010100,
    0x2048440040820001,
    0x101002200408200,
    0x40802000401080,
    0x4008142004410100,
    0x2060820c0120200,
    0x1001004080100,
    0x20c020080040080,
    0x2935610830022400,
    0x44440041009200,
    0x280001040802101,
    0x2100190040002085,
    0x80c0084100102001,
    0x4024081001000421,
    0x20030a0244872,
    0x12001008414402,
    0x2006104900a0804,
    0x1004081002402
];


// Bit count function
fn count_bits(board: BitBoard) -> usize {
    board.count_ones() as usize
} 

fn index_lsb(board: BitBoard) -> Result<usize, Error> {
    if board.trailing_zeros() == 64 {
        Err(Error::ZeroBitError)
    }else {
        Ok(board.trailing_zeros() as usize)
    }
}

// Print bitboard 
fn print_bitboard(board: BitBoard) {
    println!();
    // Loop over ranks
    for rank in (0..8).rev() {
        // Loop over files
        for file in 0..8 {
            // Convert file and rank to square number
            let square: u64 = rank * 8 + file;

            // print file markers
            if file == 0 {
                print!(" {}  ", rank+1);
            }
            // print bit state (1 or 0)
            print!(" {} ", get_bit!(board, square));
        }

        println!();
    }

    println!("\n     a  b  c  d  e  f  g  h");
    println!("\n     BitBoard: {}", board);
}

// print actual board
fn print_board() {
    println!();
    // loop over board ranks
    for rank in  (0..8).rev() {
        for file in 0..8 {
            // init square
            let square: u64 = rank * 8 + file;

            if file == 0 {
                print!(" {}  ", rank+1);
            }

            // define piece variable
            let mut piece: i32 = -1;

            // loop over all piece bitboards
            for i in (Piece::P as usize)..=(Piece::k as usize) {
                unsafe {
                    if get_bit!(PIECE_BITBOARDS[i], square) == 1 {
                        piece = i as i32;
                    }
                }
                
            }

            if piece == -1 {
                print!(" . ");
            }else{
                print!(" {} ", UNICODE_PIECES[piece as usize]);
            }
        }
        println!();
    }
    println!("\n     a  b  c  d  e  f  g  h");
    unsafe {
        if SIDE == 0 {
            println!("\n     Side to move: White");
        }else {
            println!("\n     Side to move: Black");
        }

        if ENPASSANT != BoardSquare::no_sq as u32 {
            println!("\n     Enpassant: {}", SQUARE_TO_COORD[ENPASSANT as usize]);
        }else {
            println!("\n     Enpassant: No");
        }
        print!("\n     Castling rights: ");
        if CASTLE & Castle::wk as u32 != 0 {
            print!("K")
        }else {
            print!("-")
        }
        if CASTLE & Castle::wq as u32 != 0 {
            print!(" Q");
        }else {
            print!(" -");
        }

        if CASTLE & Castle::bk as u32 != 0 {
            print!(" k");
        }else {
            print!(" -");
        }

        if CASTLE & Castle::bq as u32 != 0 {
            print!(" q\n");
        }else {
            print!(" -\n");
        }

        
    }
    
}

fn copy_board() -> ([u64; 12], [u64; 3], i32, u32, u32) {
    unsafe {
        let piece_bitboards_copy = PIECE_BITBOARDS;
        let occupancy_copy = OCCUPANCIES;
        let side_copy = SIDE;
        let enpassant_copy = ENPASSANT;
        let castle_copy = CASTLE;

        return (piece_bitboards_copy, occupancy_copy, side_copy, enpassant_copy, castle_copy)
    }
}

fn take_back(piece_bitboards_copy: [u64; 12], occupancy_copy: [u64; 3], side_copy: i32, enpassant_copy: u32, castle_copy: u32) {
    unsafe {
        PIECE_BITBOARDS = piece_bitboards_copy;
        OCCUPANCIES = occupancy_copy;
        SIDE =side_copy;
        ENPASSANT = enpassant_copy;
        CASTLE = castle_copy;
    }
}

// parse FEN string
fn parse_fen(fen: &str, char_pieces: &HashMap<char, u32>) {
    unsafe {
        PIECE_BITBOARDS = [0; 12];
        OCCUPANCIES = [0; 3];
        SIDE = 0;
        ENPASSANT = BoardSquare::no_sq as u32;
        CASTLE = 0;
        let mut fen_ptr = 0;
        let mut rank = 7;
        let mut file = 0;

        while rank >= 0 {
            while file <= 7 {
                let square = rank * 8 + file;

                if (fen.chars().nth(fen_ptr).unwrap() >= 'a' && fen.chars().nth(fen_ptr).unwrap() <= 'z') || (fen.chars().nth(fen_ptr).unwrap() >= 'A' && fen.chars().nth(fen_ptr).unwrap()<= 'Z') {
                    let piece = *char_pieces.get(&fen.chars().nth(fen_ptr).unwrap()).unwrap() as usize;

                    set_bit!(PIECE_BITBOARDS[piece], square);

                    fen_ptr += 1;

                    file += 1;
                }

                else if fen.chars().nth(fen_ptr).unwrap() >= '0' && fen.chars().nth(fen_ptr).unwrap() <= '9' {
                    let offset = (fen.chars().nth(fen_ptr).unwrap() as i32) - ('0' as i32);
                 
                    file += offset;

                    fen_ptr += 1;
                }

                else if fen.chars().nth(fen_ptr).unwrap() == '/' {
                    fen_ptr += 1;
                }
            }
            file = 0;
            rank -= 1;
        }
        fen_ptr += 1;

        if fen.chars().nth(fen_ptr).unwrap() == 'w' {
            SIDE = PieceColor::WHITE as i32;
        }else{
            SIDE = PieceColor::BLACK as i32;
        }

        fen_ptr += 2;

        while fen.chars().nth(fen_ptr).unwrap() != ' ' {
            match fen.chars().nth(fen_ptr).unwrap() {
                'K' => {CASTLE |= Castle::wk as u32;},
                'Q' => {CASTLE |= Castle::wq as u32;},
                'k' => {CASTLE |= Castle::bk as u32;},
                'q' => {CASTLE |= Castle::bq as u32;},
                '-' => {},
                _ => panic!()

            }
            fen_ptr += 1;
        }

        fen_ptr += 1;

        if fen.chars().nth(fen_ptr).unwrap() != '-' {
            let file = fen.chars().nth(fen_ptr).unwrap() as u8 - 'a' as u8;
            let rank = (fen.chars().nth(fen_ptr+1).unwrap() as u16 - '0' as u16) - 1;
            ENPASSANT = (rank * 8 + file as u16) as u32;

        }else {
            ENPASSANT = BoardSquare::no_sq as u32;
        }


        for piece in (Piece::P as usize)..=(Piece::K as usize) {
            OCCUPANCIES[PieceColor::WHITE as usize] |= PIECE_BITBOARDS[piece as usize];
        }

        for piece in (Piece::p as usize)..=(Piece::k as usize) {
            OCCUPANCIES[PieceColor::BLACK as usize] |= PIECE_BITBOARDS[piece as usize];
        }

        OCCUPANCIES[PieceColor::BOTH as usize] |= OCCUPANCIES[PieceColor::WHITE as usize];
        OCCUPANCIES[PieceColor::BOTH as usize] |= OCCUPANCIES[PieceColor::BLACK as usize];
    }
}

// Generate pawn attacks
fn mask_pawn_attacks(square: u64, side: PieceColor) -> BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;
    // Piece board
    let mut board: BitBoard = 0;

    // set piece on board
    set_bit!(board, square);

    // generate attack map
    if side as u64 == PieceColor::WHITE as u64 {
        if (board & NOT_A_FILE) != 0 {
            attacks |= board << 7;
        }

        if (board & NOT_H_FILE) != 0 {
            attacks |= board << 9;
        }
        
    }else {
        if (board & NOT_H_FILE) != 0 {
            attacks |= board >> 7;
        }

        if (board & NOT_A_FILE) != 0 {
            attacks |= board >> 9;
        }
        
    }

    attacks
}

// Generate knight attacks table
fn mask_knight_attacks(square: u64) -> BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;
    // Piece board
    let mut board: BitBoard = 0;

    // set piece on board
    set_bit!(board, square);

    //forward knight moves
    if board & NOT_H_FILE != 0 {
        attacks |= board << 17;
    }

    if board & NOT_A_FILE != 0 {
        attacks |= board << 15;
    }

    if board & NOT_HG_FILE != 0 {
        attacks |= board << 10;
    }

    if board & NOT_AB_FILE != 0 {
        attacks |= board << 6;
    }

    // backward knight moves
    if board & NOT_A_FILE != 0 {
        attacks |= board >> 17;
    }

    if board & NOT_H_FILE != 0 {
        attacks |= board >> 15;
    }

    if board & NOT_AB_FILE != 0 {
        attacks |= board >> 10;
    }

    if board & NOT_HG_FILE != 0 {
        attacks |= board >> 6;
    }
    
    

    attacks
}

fn mask_king_attacks(square: u64) ->BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;
    // Piece board
    let mut board: BitBoard = 0;

    // set piece on board
    set_bit!(board, square);

    // Forward king moves
    if board << 8 != 0 {
        attacks |= board << 8; 
    }
    if (board << 9) & NOT_A_FILE != 0 {
        attacks |= board << 9; 
    }

    if (board << 7) & NOT_H_FILE  != 0 {
        attacks |= board << 7; 
    }

    if (board << 1) & NOT_A_FILE != 0 {
        attacks |= board << 1; 
    }

    // Backward king moves
    if board >> 8 != 0 {
        attacks |= board >> 8; 
    }
    if (board >> 9) & NOT_H_FILE != 0 {
        attacks |= board >> 9; 
    }

    if (board >> 7) & NOT_A_FILE  != 0 {
        attacks |= board >> 7; 
    }

    if (board >> 1) & NOT_H_FILE != 0 {
        attacks |= board >> 1; 
    }

    attacks
}

fn mask_bishop_attacks(square: u64) -> BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;

    // Init target rank & files
    let tr:i64 = (square / 8).try_into().unwrap();
    let tf:i64 = (square % 8).try_into().unwrap();
    
    let (mut r, mut f) = (tr+1, tf+1);

    while r <= 6 && f <= 6 {
        attacks |= 1u64 << (r*8 + f);
        r += 1;
        f += 1;
    }

    (r, f) = (tr-1, tf+1);

    while r >= 1 && f <= 6 {
        attacks |= 1u64 << (r*8 + f);
        r -= 1;
        f += 1;
    }

    (r, f) = (tr+1, tf-1);

    while r <= 6 && f >= 1 {
        attacks |= 1u64 << (r*8 + f);
        r += 1;
        f -= 1;
    }

    (r, f) = (tr-1, tf-1);

    while r >= 1 && f >= 1 {
        attacks |= 1u64 << (r*8 + f);
        r -= 1;
        f -= 1;
    }

    attacks
}

fn bishop_attacks(square: u64, block: BitBoard) -> BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;

    // Init target rank & files
    let tr:i64 = (square / 8).try_into().unwrap();
    let tf:i64 = (square % 8).try_into().unwrap();
    
    let (mut r, mut f) = (tr+1, tf+1);

    while r <= 7 && f <= 7 {
        attacks |= 1u64 << (r*8 + f);
        if (1u64 << (r*8 + f)) & block != 0 {
            break;
        }
        r += 1;
        f += 1;
    }

    (r, f) = (tr-1, tf+1);

    while r >= 0 && f <= 7 {
        attacks |= 1u64 << (r*8 + f);
        if (1u64 << (r*8 + f)) & block != 0 {
            break;
        }
        r -= 1;
        f += 1;
    }

    (r, f) = (tr+1, tf-1);

    while r <= 7 && f >= 0 {
        attacks |= 1u64 << (r*8 + f);
        if (1u64 << (r*8 + f)) & block != 0 {
            break;
        }
        r += 1;
        f -= 1;
    }

    (r, f) = (tr-1, tf-1);

    while r >= 0 && f >= 0 {
        attacks |= 1u64 << (r*8 + f);
        if (1u64 << (r*8 + f)) & block != 0 {
            break;
        }
        r -= 1;
        f -= 1;
    }

    attacks
}

fn mask_rook_attacks(square: u64) -> BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;

    // Init target rank & files
    let tr:i64 = (square / 8).try_into().unwrap();
    let tf:i64 = (square % 8).try_into().unwrap();
    
    let mut r = tr+1;

    while r <= 6 {
        attacks |= 1u64 << (r*8 + tf);
        r += 1;
    }

    r = tr-1;

    while r >= 1 {
        attacks |= 1u64 << (r*8 + tf);
        r -= 1;
    }

    let mut f:i64 = tf+1;

    while f <= 6 {
        attacks |= 1u64 << (tr*8 + f);
        f += 1;
    }

    f = tf-1;

    while f >= 1 {
        attacks |= 1u64 << (tr*8 + f);
        f -= 1;
    }


    attacks
}

fn rook_attacks(square: u64, block: BitBoard) -> BitBoard {
    // Result attack board
    let mut attacks: BitBoard = 0;

    // Init target rank & files
    let tr:i64 = (square / 8).try_into().unwrap();
    let tf:i64 = (square % 8).try_into().unwrap();
    
    let mut r = tr+1;

    while r <= 7 {
        attacks |= 1u64 << (r*8 + tf);
        if (1u64 << (r*8 + tf)) & block != 0 {
            break;
        }
        r += 1;
    }

    r = tr-1;

    while r >= 0 {
        attacks |= 1u64 << (r*8 + tf);
        if (1u64 << (r*8 + tf)) & block != 0 {
            break;
        }
        r -= 1;
    }

    let mut f:i64 = tf+1;

    while f <= 7 {
        attacks |= 1u64 << (tr*8 + f);
        if (1u64 << (tr*8 + f)) & block  != 0 {
            break;
        }
        f += 1;
    }

    f = tf-1;

    while f >= 0 {
        attacks |= 1u64 << (tr*8 + f);
        if (1u64 << (tr*8 + f)) & block != 0 {
            break;
        }
        f -= 1;
    }


    attacks
}

fn set_occupancy(index: usize, n_bits_mask: usize, mut attack_mask:BitBoard) -> BitBoard {
    let mut occupancy = 0;
    // Loop over the range of bits within the attack mask
    for count in 0..n_bits_mask {
        // get LS1B index of attacks mask
        let square: usize = match index_lsb(attack_mask) {
            Ok(val) => val,
            Err(_) => return 0,
        };
        // pop LS1B in attack map
        reset_bit!(attack_mask, square);
        // make sure occupancy is on board
        if (index as u64) & (1u64 << count) != 0 {
            // populate occupancy map
            occupancy |= 1u64 << square;
        }

    }

    occupancy
}



fn init_leaper_table() {
    for square in 0..64 {
        unsafe {
            // Pawn attacks table generation
            PAWN_ATTACKS[PieceColor::WHITE as usize][square] = mask_pawn_attacks(square as u64, PieceColor::WHITE);
            PAWN_ATTACKS[PieceColor::BLACK as usize][square] = mask_pawn_attacks(square as u64, PieceColor::BLACK);
            // Knight attacks table generation
            KNIGHT_ATTACKS[square] = mask_knight_attacks(square as u64);
            // King attacks table generation
            KING_ATTACKS[square] = mask_king_attacks(square as u64);

        }
        
    }
}

fn init_sliders_table(bishop_flag: u8) {
    for square in 0..64 {
        // init bishop & rook masks
        unsafe {
            BISHOP_MASKS[square] = mask_bishop_attacks(square as u64);
            ROOK_MASKS[square] = mask_rook_attacks(square as u64);

            // init current mask
            let attack_mask = match bishop_flag {
                1 => BISHOP_MASKS[square as usize],
                0 => ROOK_MASKS[square as usize],
                _ => panic!(),
            };

            let relevant_bits_count = count_bits(attack_mask);

            let occupancy_indices = 1 << relevant_bits_count;

            for index in 0..occupancy_indices {
                if bishop_flag == 1 {
                    // init current occupancy variation
                    let occupancy = set_occupancy(index, relevant_bits_count, attack_mask);

                    // init magic index
                    let magic_index = (occupancy.wrapping_mul(BISHOP_MAGIC_NUMBERS[square as usize])) >> (64 - BISHOP_RELEVANT_BITS[square as usize]);

                    // init bishop attacks
                    BISHOP_ATTACKS[square as usize][magic_index as usize] = bishop_attacks(square as u64, occupancy);
                }else {
                    let occupancy = set_occupancy(index, relevant_bits_count, attack_mask);

                    // init magic index
                    let magic_index = (occupancy.wrapping_mul(ROOK_MAGIC_NUMBERS[square as usize])) >> (64 - ROOK_RELEVANT_BITS[square as usize]);

                    // init bishop attacks
                    ROOK_ATTACKS[square as usize][magic_index as usize] = rook_attacks(square as u64, occupancy);
                }
            }
        }

        
        
    }
}

fn get_bishop_attacks(square: u64, mut occupancy: u64)-> BitBoard {
    
    unsafe {
        occupancy &= BISHOP_MASKS[square as usize];
        occupancy =  occupancy.wrapping_mul(BISHOP_MAGIC_NUMBERS[square as usize]);
        occupancy >>= 64 - BISHOP_RELEVANT_BITS[square as usize];
        BISHOP_ATTACKS[square as usize][occupancy as usize]
    }   
    
}

// get queen attacks
fn get_rook_attacks(square: u64,mut occupancy: u64) -> BitBoard {
    unsafe {
        occupancy &= ROOK_MASKS[square as usize];
        occupancy =  occupancy.wrapping_mul(ROOK_MAGIC_NUMBERS[square as usize]);
        occupancy >>= 64 - ROOK_RELEVANT_BITS[square as usize];
        ROOK_ATTACKS[square as usize][occupancy as usize]
    }  
}


fn get_queen_attacks(square: u64, mut occupancy: u64)-> BitBoard {
    // init result attacks bitboard
    let mut queen_attacks: BitBoard = 0;

    // init bishop occupancies
    let mut bishop_occupancy = occupancy;

    // init rook occupancies
    let mut rook_occupancy = occupancy;

    
    unsafe {
        // get bishop attacks assuming current board occupancy
        bishop_occupancy &= BISHOP_MASKS[square as usize];
        bishop_occupancy = bishop_occupancy.wrapping_mul(BISHOP_MAGIC_NUMBERS[square as usize]);
        bishop_occupancy >>= 64 - BISHOP_RELEVANT_BITS[square as usize];

        // get bishop attacks
        queen_attacks = BISHOP_ATTACKS[square as usize][bishop_occupancy as usize];

        // get rook attacks assuming current board occupancy
        rook_occupancy &= ROOK_MASKS[square as usize];
        rook_occupancy = rook_occupancy.wrapping_mul(ROOK_MAGIC_NUMBERS[square as usize]);
        rook_occupancy >>= 64 - ROOK_RELEVANT_BITS[square as usize];

        // get rook attacks
        queen_attacks |= ROOK_ATTACKS[square as usize][rook_occupancy as usize];
    }

    queen_attacks
}

// evaluates if given square is attacked by given side
fn is_square_attacked(square: u64, side: u64) -> bool {
    unsafe {
        // attacked by white pawns
        if (side == PieceColor::WHITE as u64) && (PAWN_ATTACKS[PieceColor::BLACK as usize][square as usize] & PIECE_BITBOARDS[Piece::P as usize] != 0) {
            return true;
        }

        // attacked by black pawns
        if (side == PieceColor::BLACK as u64) && (PAWN_ATTACKS[PieceColor::WHITE as usize][square as usize] & PIECE_BITBOARDS[Piece::p as usize] != 0) {
            return true;
        }
        // attacked by knights
        let knight_occupancy = match side {
            0 => PIECE_BITBOARDS[Piece::N as usize],
            1 => PIECE_BITBOARDS[Piece::n as usize],
            _ => 0,
        };
        if KNIGHT_ATTACKS[square as usize] & knight_occupancy != 0 {
            return true;
        }

        // attacked by bishops
        let bishop_occupancy = match side {
            0 => PIECE_BITBOARDS[Piece::B as usize],
            1 => PIECE_BITBOARDS[Piece::b as usize],
            _ => 0,
        };

        if get_bishop_attacks(square, OCCUPANCIES[PieceColor::BOTH as usize]) & bishop_occupancy != 0 {
            return true;
        }
        
        // attacked by rooks
        let rook_occupancy = match side {
            0 => PIECE_BITBOARDS[Piece::R as usize],
            1 => PIECE_BITBOARDS[Piece::r as usize],
            _ => 0,
        };

        if get_rook_attacks(square, OCCUPANCIES[PieceColor::BOTH as usize]) & rook_occupancy != 0{
            return true;
        }

        // attacked by queens
        let queen_occupancy = match side {
            0 => PIECE_BITBOARDS[Piece::Q as usize],
            1 => PIECE_BITBOARDS[Piece::q as usize],
            _ => 0,
        };

        if get_queen_attacks(square, OCCUPANCIES[PieceColor::BOTH as usize]) & queen_occupancy != 0{
            return true;
        }

        // attacked by kings
        let king_occupancy = match side {
            0 => PIECE_BITBOARDS[Piece::K as usize],
            1 => PIECE_BITBOARDS[Piece::k as usize],
            _ => 0,
        };
        if KING_ATTACKS[square as usize] & king_occupancy != 0 {
            return true;
        }
        // by default return false
        false
    }
    
}

fn print_attacked_squares(side: u64){
    println!();
    // Loop over ranks
    for rank in (0..8).rev() {
        // Loop over files
        for file in 0..8 {
            // Convert file and rank to square number
            let square: u64 = rank * 8 + file;

            // print file markers
            if file == 0 {
                print!(" {}  ", rank+1);
            }
            // print bit state (1 or 0)
            print!(" {} ", is_square_attacked(square, side) as u64);
        }

        println!();
    }

    println!("\n     a  b  c  d  e  f  g  h");
}


fn generate_moves() -> Vec<u64>{
    // defining move list
    let mut move_list = Vec::<u64>::new();
    // define source & target squares
    let mut source_square = BoardSquare::no_sq as u64;
    let mut target_square = BoardSquare::no_sq as u64;

    // define current piece's bitboard copy & it's attacks
    let mut bitboard: BitBoard = 0;
    let mut attacks = 0;

    for piece in Piece::P as usize..=(Piece::k as usize) {
        unsafe {
            // init piece bitboard copy
            bitboard = PIECE_BITBOARDS[piece].clone();
            // generate white pawns & white king castling moves
            if SIDE == PieceColor::WHITE as i32 {
                if piece == Piece::P as usize {
                    while bitboard != 0 {
                        // init source square
                        source_square = match index_lsb(bitboard) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };

                        // init target square
                        target_square = source_square + 8;

                        // generate quiet pawn moves
                        if !(target_square < BoardSquare::a1 as u64) && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], target_square) == 0 {
                            // pawn promotion
                            if source_square >= BoardSquare::a7 as u64 && source_square <= BoardSquare::h7 as u64 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64){
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::Q as u64, 0, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::R as u64, 0, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::B as u64, 0, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::N as u64, 0, 0, 0, 0));
                                }
                                
                            }else{
                                // one square ahead pawn move
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                

                                // two squares ahead pawn move
                                if (source_square >= BoardSquare::a2 as u64 && source_square <= BoardSquare::h2 as u64) && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], target_square + 8) == 0 {
                                    if !is_piece_pinned_absolute(source_square, target_square+8, SIDE as u64) {
                                        move_list.push(encode_move!(source_square, target_square +8, piece as u64, 0, 0, 1, 0, 0));
                                    }
                                    
                                }
                            }
                        }

                        // init pawn attacks bitboard
                        attacks = PAWN_ATTACKS[SIDE as usize][source_square as usize] & OCCUPANCIES[PieceColor::BLACK as usize]; 

                        // generate pawn captures

                        while attacks != 0 {
                            // init target square 
                            target_square = match index_lsb(attacks) {
                                Ok(val) => val as u64,
                                Err(_) => panic!(),
                            };

                            if source_square >= BoardSquare::a7 as u64 && source_square <= BoardSquare::h7 as u64 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::Q as u64, 1, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::R as u64, 1, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::B as u64, 1, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::N as u64, 1, 0, 0, 0));
                                }
                                
                            }else{
                                // one square ahead pawn move
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                

                            }

                            reset_bit!(attacks, target_square);
                        }

                        // generate enpassant captures
                        if ENPASSANT != BoardSquare::no_sq as u32 {
                            let enpassant_attacks = PAWN_ATTACKS[SIDE as usize][source_square as usize] & (1 << ENPASSANT);
                            // make sure enpassant capture available
                            if enpassant_attacks != 0 {
                                // init enpassant capture target square
                                let target_enpassant = match index_lsb(enpassant_attacks) {
                                    Ok(val) => val as u64,
                                    Err(_) => panic!()
                                };
                                if !is_piece_pinned_absolute(source_square, target_enpassant, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_enpassant, piece as u64, 0, 1, 0, 1, 0));
                                }
                            }
                        }

                        reset_bit!(bitboard, source_square);
                    }
                // castling moves
                }
                if piece == Piece::K as usize {
                    // king side castling is available
                    if CASTLE & Castle::wk as u32 != 0  {
                        // make sure square between king and king's rook are empty
                        if get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::f1 as u64) == 0 && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::g1 as u64) == 0 {
                            // make sure king and the f1 & g1 squares are not under attacks
                            if !is_square_attacked(BoardSquare::e1 as u64, PieceColor::BLACK as u64) && !is_square_attacked(BoardSquare::f1 as u64, PieceColor::BLACK as u64) && !is_square_attacked(BoardSquare::g1 as u64, PieceColor::BLACK as u64) {
                                // println!("castling move: e1g1");
                                move_list.push(encode_move!(BoardSquare::e1 as u64, BoardSquare::g1 as u64, piece as u64, 0, 0, 0, 0, 1));
                            }
                        }
                    }
                    // queen side castling is available
                    if CASTLE & Castle::wq as u32 != 0 {
                        // make sure square between king and queen's rook are empty
                        if get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::d1 as u64) == 0 && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::c1 as u64) == 0 && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::b1 as u64) == 0 {
                            // make sure king and the d1 & c1 squares are not under attacks
                            if !is_square_attacked(BoardSquare::e1 as u64, PieceColor::BLACK as u64) && !is_square_attacked(BoardSquare::d1 as u64, PieceColor::BLACK as u64) && !is_square_attacked(BoardSquare::c1 as u64, PieceColor::BLACK as u64) {
                                move_list.push(encode_move!(BoardSquare::e1 as u64, BoardSquare::c1 as u64, piece as u64, 0, 0, 0, 0, 1));
                            }
                        }
                    } 
                }

            // generate black pawns & black king castling moves
            }else {
                if piece == Piece::p as usize {
                    while bitboard != 0 {
                        // init source square
                        source_square = match index_lsb(bitboard) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };

                        // init target square
                        target_square = source_square - 8;

                        if !(target_square > BoardSquare::h8 as u64) && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], target_square) == 0 {

                            if source_square >= BoardSquare::a2 as u64 && source_square <= BoardSquare::h2 as u64 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::q as u64, 0, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::r as u64, 0, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::b as u64, 0, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::n as u64, 0, 0, 0, 0));
                                }
                                
                            }else{
                                // one square ahead pawn move
                                if !is_piece_pinned_absolute(source_square, target_square, PieceColor::BLACK as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                

                                // two squares ahead pawn move
                                if (source_square >= BoardSquare::a7 as u64 && source_square <= BoardSquare::h7 as u64) && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], target_square - 8) == 0 {
                                    if !is_piece_pinned_absolute(source_square, target_square - 8, SIDE as u64) {
                                        move_list.push(encode_move!(source_square, target_square-8, piece as u64, 0, 0, 1, 0, 0));
                                    }
                                    
                                }
                            }
                        }

                        attacks = PAWN_ATTACKS[SIDE as usize][source_square as usize] & OCCUPANCIES[PieceColor::WHITE as usize]; 

                        // generate pawn captures

                        while attacks != 0 {
                            // init target square 
                            target_square = match index_lsb(attacks) {
                                Ok(val) => val as u64,
                                Err(_) => panic!(),
                            };

                            if source_square >= BoardSquare::a2 as u64 && source_square <= BoardSquare::h2 as u64 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::q as u64, 1, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::r as u64, 1, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::b as u64, 1, 0, 0, 0));
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, Piece::n as u64, 1, 0, 0, 0));
                                }
                                
                            }else{
                                // one square ahead pawn move
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                

                            }

                            reset_bit!(attacks, target_square);
                        }

                        // generate enpassant captures
                        if ENPASSANT != BoardSquare::no_sq as u32 {
                            let enpassant_attacks = PAWN_ATTACKS[SIDE as usize][source_square as usize] & (1 << ENPASSANT);
                            // make sure enpassant capture available
                            if enpassant_attacks != 0 {
                                // init enpassant capture target square
                                let target_enpassant = match index_lsb(enpassant_attacks) {
                                    Ok(val) => val as u64,
                                    Err(_) => panic!()
                                };

                                if !is_piece_pinned_absolute(source_square, target_enpassant, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_enpassant, piece as u64, 0, 1, 0, 1, 0));
                                }
                                
                            }
                        }

                        reset_bit!(bitboard, source_square);
                    }
                }
                if piece == Piece::k as usize {
                    // king side castling is available
                    if CASTLE & Castle::bk as u32 != 0  {
                        // make sure square between king and king's rook are empty
                        if get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::f8 as u64) == 0 && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::g8 as u64) == 0 {
                            // make sure king and the f8 & g8 squares are not under attack
                            if !is_square_attacked(BoardSquare::e8 as u64, PieceColor::WHITE as u64) && !is_square_attacked(BoardSquare::f8 as u64, PieceColor::WHITE as u64) && !is_square_attacked(BoardSquare::g8 as u64, PieceColor::WHITE as u64) {
                                move_list.push(encode_move!(BoardSquare::e8 as u64, BoardSquare::g8 as u64, piece as u64, 0, 0, 0, 0, 1));
                            }
                        }
                    }
                    // queen side castling is available
                    if CASTLE & Castle::bq as u32 != 0 {
                        // make sure square between king and queen's rook are empty
                        if get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::d8 as u64) == 0 && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::c8 as u64) == 0 && get_bit!(OCCUPANCIES[PieceColor::BOTH as usize], BoardSquare::b8 as u64) == 0 {
                            // make sure king and the d8 & c8 squares are not under attack
                            if !is_square_attacked(BoardSquare::e8 as u64, PieceColor::WHITE as u64) && !is_square_attacked(BoardSquare::d8 as u64, PieceColor::WHITE as u64) && !is_square_attacked(BoardSquare::c8 as u64, PieceColor::WHITE as u64) {
                                move_list.push(encode_move!(BoardSquare::e8 as u64, BoardSquare::c8 as u64, piece as u64, 0, 0, 0, 0, 1));
                            }
                        }
                    } 
                }

            }
            // genarate knight moves
            if (SIDE == PieceColor::WHITE as i32 && piece == Piece::N as usize) || (SIDE == PieceColor::BLACK as i32 && piece == Piece::n as usize) {
                // loop over source squares of piece bitboard copy
                while bitboard != 0 {
                    // init source square
                    source_square = match index_lsb(bitboard) {
                        Ok(val) => val as u64,
                        Err(_) => panic!(),
                    };

                    // init piece attacks in order to get set of target squares
                    if SIDE == PieceColor::WHITE as i32 {
                        attacks = KNIGHT_ATTACKS[source_square as usize] & !OCCUPANCIES[PieceColor::WHITE as usize];
                    }else {
                        attacks = KNIGHT_ATTACKS[source_square as usize] & !OCCUPANCIES[PieceColor::BLACK as usize];
                    }

                    // loop over target squares available from generated attacks
                    while attacks != 0 {
                        // init target square
                        target_square = match index_lsb(attacks) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };

                        // quiet move
                        if SIDE == PieceColor::WHITE as i32 {
                            if get_bit!(OCCUPANCIES[PieceColor::BLACK as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }else {
                            if get_bit!(OCCUPANCIES[PieceColor::WHITE as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }

                        reset_bit!(attacks, target_square);
                    }

                    reset_bit!(bitboard, source_square);
                }
            }

            // generate bishop moves
            if (SIDE == PieceColor::WHITE as i32 && piece == Piece::B as usize) || (SIDE == PieceColor::BLACK as i32 && piece == Piece::b as usize) {
                // loop over source squares of piece bitboard copy
                while bitboard != 0 {
                    // init source square
                    source_square = match index_lsb(bitboard) {
                        Ok(val) => val as u64,
                        Err(_) => panic!(),
                    };
                    // init piece attacks in order to get set of target squares
                    if SIDE == PieceColor::WHITE as i32 {
                        attacks = get_bishop_attacks(source_square, OCCUPANCIES[PieceColor::BOTH as usize]) & !OCCUPANCIES[PieceColor::WHITE as usize];
                    }else {
                        attacks = get_bishop_attacks(source_square, OCCUPANCIES[PieceColor::BOTH as usize]) & !OCCUPANCIES[PieceColor::BLACK as usize];
                    }

                    while attacks != 0 {
                        // init target square
                        target_square = match index_lsb(attacks) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };

                        // quiet move
                        if SIDE == PieceColor::WHITE as i32 {
                            if get_bit!(OCCUPANCIES[PieceColor::BLACK as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }else {
                            if get_bit!(OCCUPANCIES[PieceColor::WHITE as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }

                        reset_bit!(attacks, target_square);
                    }

                    reset_bit!(bitboard, source_square);
                }
            }

            // generate rook moves
            if (SIDE == PieceColor::WHITE as i32 && piece == Piece::R as usize) || (SIDE == PieceColor::BLACK as i32 && piece == Piece::r as usize) {
                // loop over source squares of piece bitboard copy
                while bitboard != 0 {
                    // init source square
                    source_square = match index_lsb(bitboard) {
                        Ok(val) => val as u64,
                        Err(_) => panic!(),
                    };
                    // init piece attacks in order to get set of target squares
                    if SIDE == PieceColor::WHITE as i32 {
                        attacks = get_rook_attacks(source_square, OCCUPANCIES[PieceColor::BOTH as usize]) & !OCCUPANCIES[PieceColor::WHITE as usize];
                    }else {
                        attacks = get_rook_attacks(source_square, OCCUPANCIES[PieceColor::BOTH as usize]) & !OCCUPANCIES[PieceColor::BLACK as usize];
                    }

                    while attacks != 0 {
                        // init target square
                        target_square = match index_lsb(attacks) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };

                        // quiet move
                        if SIDE == PieceColor::WHITE as i32 {
                            if get_bit!(OCCUPANCIES[PieceColor::BLACK as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }else {
                            if get_bit!(OCCUPANCIES[PieceColor::WHITE as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }

                        reset_bit!(attacks, target_square);
                    }

                    reset_bit!(bitboard, source_square);
                }
            }

            // generate queen moves
            if (SIDE == PieceColor::WHITE as i32 && piece == Piece::Q as usize) || (SIDE == PieceColor::BLACK as i32 && piece == Piece::q as usize) {
                // loop over source squares of piece bitboard copy
                while bitboard != 0 {
                    // init source square
                    source_square = match index_lsb(bitboard) {
                        Ok(val) => val as u64,
                        Err(_) => panic!(),
                    };
                    // init piece attacks in order to get set of target squares
                    if SIDE == PieceColor::WHITE as i32 {
                        attacks = get_queen_attacks(source_square, OCCUPANCIES[PieceColor::BOTH as usize]) & !OCCUPANCIES[PieceColor::WHITE as usize];
                    }else {
                        attacks = get_queen_attacks(source_square, OCCUPANCIES[PieceColor::BOTH as usize]) & !OCCUPANCIES[PieceColor::BLACK as usize];
                    }
    
                    while attacks != 0 {
                        // init target square
                        target_square = match index_lsb(attacks) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };
    
                        // quiet move
                        if SIDE == PieceColor::WHITE as i32 {
                            if get_bit!(OCCUPANCIES[PieceColor::BLACK as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square,SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }   
                                
                            }
                        }else {
                            if get_bit!(OCCUPANCIES[PieceColor::WHITE as usize], target_square) == 0 {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                                }
                                
                            }else {
                                if !is_piece_pinned_absolute(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }
    
                        reset_bit!(attacks, target_square);
                    }
    
                    reset_bit!(bitboard, source_square);
                }
            }

            // generate king moves
            if (SIDE == PieceColor::WHITE as i32 && piece == Piece::K as usize) || (SIDE == PieceColor::BLACK as i32 && piece == Piece::k as usize) {
                // loop over source squares of piece bitboard copy
                while bitboard != 0 {
                    // init source square
                    source_square = match index_lsb(bitboard) {
                        Ok(val) => val as u64,
                        Err(_) => panic!(),
                    };

                    // init piece attacks in order to get set of target squares
                    if SIDE == PieceColor::WHITE as i32 {
                        attacks = KING_ATTACKS[source_square as usize] & !OCCUPANCIES[PieceColor::WHITE as usize]
                    }else {
                        attacks = KING_ATTACKS[source_square as usize] & !OCCUPANCIES[PieceColor::BLACK as usize]
                    }

                    // loop over target squares available from generated attacks
                    while attacks != 0 {
                        // init target square
                        target_square = match index_lsb(attacks) {
                            Ok(val) => val as u64,
                            Err(_) => panic!(),
                        };

                        // quiet move
                        if SIDE == PieceColor::WHITE as i32 {
                            if get_bit!(OCCUPANCIES[PieceColor::BLACK as usize], target_square) == 0 && !is_square_attacked(target_square, PieceColor::BLACK as u64) && !is_king_in_check(source_square, target_square, SIDE as u64){
                                move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                            }else {
                                if !is_square_attacked(target_square, PieceColor::BLACK as u64) && !is_king_in_check(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                                
                            }
                        }else {
                            if get_bit!(OCCUPANCIES[PieceColor::WHITE as usize], target_square) == 0 && !is_square_attacked(target_square, PieceColor::WHITE as u64) && !is_king_in_check(source_square, target_square, SIDE as u64)  {
                                move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 0, 0, 0, 0));
                            }else {
                                if !is_square_attacked(target_square, PieceColor::WHITE as u64) && !is_king_in_check(source_square, target_square, SIDE as u64) {
                                    move_list.push(encode_move!(source_square, target_square, piece as u64, 0, 1, 0, 0, 0));
                                }
                            }
                        }

                        reset_bit!(attacks, target_square);
                    }

                    reset_bit!(bitboard, source_square);
                }
            }
        }

    }
    move_list
}

// (for UCI purposes)
fn get_uci_move(ch_move: u64) -> String {

    let promoted = get_move_promoted!(ch_move);

    let promoted_piece = match ASCII_PIECES[promoted as usize] {
        "Q" => "q",
        "R" => "r",
        "B" => "b",
        "N" => "n",
        "q" => "q",
        "r" => "r",
        "b" => "b",
        "n" => "n",
        _ => ""
    };
    
    let uci_move = format!("{}{}{}", 
    SQUARE_TO_COORD[get_move_source!(ch_move) as usize],
    SQUARE_TO_COORD[get_move_target!(ch_move) as usize],
    promoted_piece,
    );

    return uci_move;
}


fn make_move(ch_move: u64, move_flag: MOVE_TYPE) -> bool {
    // Quiet moves
    unsafe {
        if move_flag == MOVE_TYPE::all_moves {
            // Preserve board state
            // Parse move
            let source_square = get_move_source!(ch_move);
            let target_square = get_move_target!(ch_move);
            let piece = get_move_piece!(ch_move);
            let promoted = get_move_promoted!(ch_move);
            let capture = get_move_capture!(ch_move);
            let double_push = get_move_double!(ch_move);
            let enpassant = get_move_enpassant!(ch_move);
            let castling = get_move_castling!(ch_move);



            // Move piece
            reset_bit!(PIECE_BITBOARDS[piece as usize], source_square);
            set_bit!(PIECE_BITBOARDS[piece as usize], target_square);

            // Handling capture moves
            if capture != 0 {
                let mut start_piece:usize = 0;
                let mut end_piece:usize = 0;

                if SIDE == PieceColor::WHITE as i32 {
                    start_piece = Piece::p as usize;
                    end_piece = Piece::k as usize;
                }else {
                    start_piece = Piece::P as usize;
                    end_piece = Piece::K as usize;
                }
                // Loop over bitboards opposite to the current side to move
                for bb_piece in start_piece..=end_piece {
                    // if there's a piece on the target square
                    if get_bit!(PIECE_BITBOARDS[bb_piece], target_square) != 0 {
                        // remove it from corresponding bitboard
                        reset_bit!(PIECE_BITBOARDS[bb_piece], target_square);
                        break;
                    }
                } 
            }
            // handle pawn promotions
            if promoted != 0 {
                if SIDE == PieceColor::WHITE as i32 {
                    reset_bit!(PIECE_BITBOARDS[Piece::P as usize], target_square);
                }else{
                    reset_bit!(PIECE_BITBOARDS[Piece::p as usize], target_square);
                }
                set_bit!(PIECE_BITBOARDS[promoted as usize], target_square);
                
            }

            // handle enpassant captures
            if enpassant != 0 {
                // erase the pawn depending on side to move
                if SIDE == PieceColor::WHITE as i32 {
                    reset_bit!(PIECE_BITBOARDS[Piece::p as usize], target_square-8);
                }else {
                    reset_bit!(PIECE_BITBOARDS[Piece::P as usize], target_square+8);
                }
            }

            // Reset enpassant square
            ENPASSANT = BoardSquare::no_sq as u32;


            // handle double pawn push
            if double_push != 0 {
                // set enpassant aquare depending on side to move
                if SIDE == PieceColor::WHITE as i32 {
                    ENPASSANT = target_square as u32 - 8 ;
                }else {
                    ENPASSANT = target_square as u32 + 8 ;
                }
            }

            // handle castling moves
            if castling != 0 {
                match target_square {
                    // white castles king side
                    // BoardSquare::g1 
                    6  => {
                        // move H rook
                        reset_bit!(PIECE_BITBOARDS[Piece::R as usize], BoardSquare::h1);
                        set_bit!(PIECE_BITBOARDS[Piece::R as usize], BoardSquare::f1);
                    },

                    // white castles queen side
                    // BoardSquare::c1
                    2 => {
                        // move A rook
                        reset_bit!(PIECE_BITBOARDS[Piece::R as usize], BoardSquare::a1);
                        set_bit!(PIECE_BITBOARDS[Piece::R as usize], BoardSquare::d1);
                    },

                    // black castles king side
                    // BoardSquare::g8
                    62 => {
                        // move H rook
                        reset_bit!(PIECE_BITBOARDS[Piece::r as usize], BoardSquare::h8);
                        set_bit!(PIECE_BITBOARDS[Piece::r as usize], BoardSquare::f8);
                    },

                    // black castles queen side
                    // BoardSquare::c8
                    58 => {
                        // move A rook
                        reset_bit!(PIECE_BITBOARDS[Piece::r as usize], BoardSquare::a8);
                        set_bit!(PIECE_BITBOARDS[Piece::r as usize], BoardSquare::d8);
                    },

                    _ => {}
                }
                
            }

            // update castling rights
            CASTLE &=  CASTLING_RIGHTS[source_square as usize];
            CASTLE &=  CASTLING_RIGHTS[target_square as usize];

            // reset occupancies
            OCCUPANCIES = [0; 3];

            // loop over white pieces bitboards
            for bb_piece in Piece::P as usize..=Piece::K as usize {
                // update white occupancies
                OCCUPANCIES[PieceColor::WHITE as usize] |= PIECE_BITBOARDS[bb_piece];
            }

            // loop over black pieces bitboards
            for bb_piece in Piece::p as usize..=Piece::k as usize {
                // update white occupancies
                OCCUPANCIES[PieceColor::BLACK as usize] |= PIECE_BITBOARDS[bb_piece];
            }

            // update both sides occupancies
            OCCUPANCIES[PieceColor::BOTH as usize] |= OCCUPANCIES[PieceColor::WHITE as usize];
            OCCUPANCIES[PieceColor::BOTH as usize] |= OCCUPANCIES[PieceColor::BLACK as usize];

            // change side
            SIDE ^= 1;

            return true;

        // Capture moves
        } else {
            // Make sure move is the capture
            if get_move_capture!(ch_move) != 0{
                return make_move(ch_move, MOVE_TYPE::all_moves);
                //return true;
            // Otherwise the move is not a capture
            }else {
                // Don't make it
                return false;
            }
        }
    }
    
}

fn perft_driver(depth: u64, root: bool) -> usize {
    let mut cnt = 0;
    let mut nodes = 0;

    let leaf = match depth {
        2 => true,
        _ => false,
    };

    for mv in generate_moves() {
        if root && depth <= 1 {
            cnt = 1;
            nodes += 1
        }else {
            let (piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy) = copy_board();
            make_move(mv, MOVE_TYPE::all_moves);
            if leaf {
                
                cnt = generate_moves().len();
                
            }else {
                cnt = perft_driver(depth -1, false);
            }

            nodes += cnt;
            
            take_back(piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy);
        }

        if root {
            println!("{}{}: {}", SQUARE_TO_COORD[get_move_source!(mv) as usize], SQUARE_TO_COORD[get_move_target!(mv) as usize], cnt);
        }
    }

    nodes


}


fn init_char_pieces(map: &mut HashMap<char, u32>) {
    map.insert('P', 0);
    map.insert('N', 1);
    map.insert('B', 2);
    map.insert('R', 3);
    map.insert('Q', 4);
    map.insert('K', 5);
    map.insert('p', 6);
    map.insert('n', 7);
    map.insert('b', 8);
    map.insert('r', 9);
    map.insert('q', 10);
    map.insert('k', 11);
}

fn get_time_ms() -> u64 {
    let start = SystemTime::now();
    let since_the_epoch = start.duration_since(UNIX_EPOCH).expect("Time is going backwards");
    since_the_epoch.as_millis() as u64
}


fn is_piece_pinned_absolute(piece_source_square: u64, piece_target_square:u64, piece_side: u64) -> bool {
    unsafe {
            // update occupancy bitboard with pinned piece move
            let mut updated_occupancy = OCCUPANCIES[PieceColor::BOTH as usize];
            reset_bit!(updated_occupancy, piece_source_square);
            set_bit!(updated_occupancy, piece_target_square);

            // update enemy piece occupancy
            let mut updated_enemy_piece_bitboards = PIECE_BITBOARDS.clone();
            if piece_side == PieceColor::WHITE as u64 {
                for bb_piece in Piece::p as usize..=Piece::k as usize {
                    // update black piece occupancies
                    reset_bit!(updated_enemy_piece_bitboards[bb_piece], piece_target_square);
                }
            }else {
                for bb_piece in Piece::P as usize..=Piece::K as usize {
                    // update white piece occupancies
                    reset_bit!(updated_enemy_piece_bitboards[bb_piece], piece_target_square);
                }
            }


            let king_occupancy = match piece_side {
                0 => PIECE_BITBOARDS[Piece::K as usize],
                1 => PIECE_BITBOARDS[Piece::k as usize],
                _ => panic!(),
            };

            // attacked by bishops
            let mut bishop_occupanices = match piece_side {
                0 => updated_enemy_piece_bitboards[Piece::b as usize],
                1 => updated_enemy_piece_bitboards[Piece::B as usize],
                _ => panic!(),
            };
            while bishop_occupanices != 0 {
                let bishop_square = match index_lsb(bishop_occupanices) {
                    Ok(val) => val as u64,
                    Err(_) => panic!()
                };
                if get_bishop_attacks(bishop_square, updated_occupancy) & king_occupancy != 0{
                    return true;
                }

                reset_bit!(bishop_occupanices, bishop_square);
            }   
            

            // attacked by rooks
            let mut rook_occupancies = match piece_side {
                0 => updated_enemy_piece_bitboards[Piece::r as usize],
                1 => updated_enemy_piece_bitboards[Piece::R as usize],
                _ => panic!(),
            };
            while rook_occupancies != 0 {
                let rook_square = match index_lsb(rook_occupancies) {
                    Ok(val) => val as u64,
                    Err(_) => panic!()
                };
                if get_rook_attacks(rook_square, updated_occupancy) & king_occupancy != 0{
                    return true;
                }

                reset_bit!(rook_occupancies, rook_square);
            }  

            // attacked by queens
            let mut queen_occupancies = match piece_side {
                0 => updated_enemy_piece_bitboards[Piece::q as usize],
                1 => updated_enemy_piece_bitboards[Piece::Q as usize],
                _ => panic!(),
            };
            while queen_occupancies != 0 {
                let queen_square = match index_lsb(queen_occupancies) {
                    Ok(val) => val as u64,
                    Err(_) => panic!()
                };
                if get_queen_attacks(queen_square, updated_occupancy) & king_occupancy != 0{
                    return true;
                }

                reset_bit!(queen_occupancies, queen_square);
            }

            // attacked by knights
            let mut knight_occupancies = match piece_side {
                0 => updated_enemy_piece_bitboards[Piece::n as usize],
                1 => updated_enemy_piece_bitboards[Piece::N as usize],
                _ => panic!(),
            };

            while knight_occupancies != 0 {
                let knight_square = match index_lsb(knight_occupancies) {
                    Ok(val) => val,
                    Err(_) => panic!()
                };

                if KNIGHT_ATTACKS[knight_square] & king_occupancy !=0 {
                    return true;
                }

                reset_bit!(knight_occupancies, knight_square);
            }

            // attacked by pawns
            let mut pawn_occupancies = match piece_side {
                0 => updated_enemy_piece_bitboards[Piece::p as usize],
                1 => updated_enemy_piece_bitboards[Piece::P as usize],
                _ => panic!(),
            };

            while pawn_occupancies != 0 {
                let pawn_square = match index_lsb(pawn_occupancies) {
                    Ok(val) => val,
                    Err(_) => panic!(),
                };
                let enemy_pawn_side = match piece_side {
                    0 => 1,
                    1 => 0,
                    _ => panic!(),
                };
                if PAWN_ATTACKS[enemy_pawn_side as usize][pawn_square] & king_occupancy != 0 {
                    return true;
                }
                reset_bit!(pawn_occupancies, pawn_square);
            }

        return false;
    }
}

fn is_king_in_check(king_source_square: u64, king_target_square: u64, king_color: u64) -> bool {
    unsafe {
        let mut updated_occupancies = OCCUPANCIES[PieceColor::BOTH as usize];

        reset_bit!(updated_occupancies, king_source_square);
        set_bit!(updated_occupancies, king_target_square);

        let mut king_occupancy = match king_color {
            0 => PIECE_BITBOARDS[Piece::K as usize],
            1 => PIECE_BITBOARDS[Piece::k as usize],
            _ => panic!(),
        };

        reset_bit!(king_occupancy, king_source_square);
        set_bit!(king_occupancy, king_target_square);
        
        // attacked by bishops
        let mut bishop_occupanices = match king_color {
            0 => PIECE_BITBOARDS[Piece::b as usize],
            1 => PIECE_BITBOARDS[Piece::B as usize],
            _ => panic!(),
        };
        while bishop_occupanices != 0 {
            let bishop_square = match index_lsb(bishop_occupanices) {
                Ok(val) => val as u64,
                Err(_) => panic!()
            };
            if get_bishop_attacks(bishop_square, updated_occupancies) & king_occupancy != 0{
                return true;
            }

            reset_bit!(bishop_occupanices, bishop_square);
        }

        // attacked by rooks
        let mut rook_occupancies = match king_color {
            0 => PIECE_BITBOARDS[Piece::r as usize],
            1 => PIECE_BITBOARDS[Piece::R as usize],
            _ => panic!(),
        };
        while rook_occupancies != 0 {
            let rook_square = match index_lsb(rook_occupancies) {
                Ok(val) => val as u64,
                Err(_) => panic!()
            };
            if get_rook_attacks(rook_square, updated_occupancies) & king_occupancy != 0{
                return true;
            }

            reset_bit!(rook_occupancies, rook_square);
        }

        // attacked by queens
        let mut queen_occupancies = match king_color {
            0 => PIECE_BITBOARDS[Piece::q as usize],
            1 => PIECE_BITBOARDS[Piece::Q as usize],
            _ => panic!(),
        };
        while queen_occupancies != 0 {
            let rook_square = match index_lsb(queen_occupancies) {
                Ok(val) => val as u64,
                Err(_) => panic!()
            };
            if get_queen_attacks(rook_square, updated_occupancies) & king_occupancy != 0{
                return true;
            }

            reset_bit!(queen_occupancies, rook_square);
        }      
        


        return false;
    }
}

// parse user/GUI move string input (e.g. "e7e8q")
fn parse_move(str_move: &str) -> Result<u64, Error>{
    let legal_moves = generate_moves();

    for mv in legal_moves {
        let legal_str_move = get_uci_move(mv);

        if legal_str_move == String::from(str_move) {
            return Ok(mv);
        }
    }

    return Err(Error::IllegalMoveError);
}

// Example UCI commands to init position on chess board
    
//     // init start position
//     position startpos
    
//     // init start position and make the moves on chess board
//     position startpos moves e2e4 e7e5
    
//     // init position from FEN string
//     position fen r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1 
    
//     // init position from fen string and make moves on chess board
//     position fen r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1 moves e2a6 e8g8

fn parse_position(command: String, char_pieces: &HashMap<char, u32>) {
    
    let start_pos = command.chars().take(17).collect::<Vec<char>>().iter().collect::<String>();

    let start_fen = command.chars().take(12).collect::<Vec<char>>().iter().collect::<String>();

    if start_pos == "position startpos" {
        parse_fen(START_POSTITION, char_pieces);

        let moves = command.chars().skip(24).collect::<Vec<char>>().iter().collect::<String>();

        if moves.chars().count() > 0 {
            for mv in moves.split(" ") {
                let ch_mv = match parse_move(mv) {
                    Ok(val) => val,
                    Err(_) => panic!("illegal move: {}", mv),
                };
                make_move(ch_mv, MOVE_TYPE::all_moves);
            }
        }
        
    }else if start_fen == "position fen" {
        let fen_pos = command.chars().skip(13).collect::<Vec<char>>().iter().collect::<String>();

        let re = Regex::new(r"^(([rnbqkpRNBQKP1-8]{1,8}/){7}[rnbqkpRNBQKP1-8]{1,8})\s[bw]\s(-|[KQkq]{1,4})\s(-|[a-h][36])\s\d+\s\d+\s*").expect("invalid regex");

        let caps = match re.find(fen_pos.as_str()) {
            Some(v) => v,
            None => return,
        };

        parse_fen(caps.as_str(), char_pieces);

        let moves = fen_pos.chars().skip(caps.end()+6).collect::<Vec<char>>().iter().collect::<String>();

        if moves.chars().count() > 0 {
            for mv in moves.split(" ") {
                let ch_mv = match parse_move(mv) {
                    Ok(val) => val,
                    Err(_) => panic!("illegal move: {}", mv),
                };
                make_move(ch_mv, MOVE_TYPE::all_moves);
            }
        }


    }
}

fn search_position(depth: usize) {

    // clear helper data structures for search
    unsafe {
        NODES = 0;
        KILLER_MOVES = [[0; 64]; 2];
        HISTORY_MOVES = [[0; 64]; 12];
        PV_TABLE = [[0; 64]; 64];
        PV_LENGTH = [0; 64];
        FOLLOW_PV = 0;
        SCORE_PV = 0;
        STOPPED = 0;
    }
    // define initial alpha beta bounds
    let mut alpha = -50000;
    let mut beta = 50000;

    // iterative deepening 
    for current_depth in 1..=depth {
        unsafe {
            if STOPPED == 1 {
                break;
            }
        }
        // find best move within a given position

        // enable follow pv flag
        unsafe {
            FOLLOW_PV = 1;
        }

        let score = negamax(alpha, beta, current_depth);

        unsafe {

            print!("info score cp {} depth {} nodes {} pv ", score, current_depth, NODES);

            for i in 0..PV_LENGTH[0] as usize {
                print!("{}", get_uci_move(PV_TABLE[0][i]));
                print!(" ");
            }
            println!();
        }

        
    }
    
    unsafe {
        BEST_MOVE = PV_TABLE[0][0];
        if get_move_promoted!(BEST_MOVE) != 0 {
            println!("bestmove {}{}{}",
            SQUARE_TO_COORD[get_move_source!(BEST_MOVE) as usize],
            SQUARE_TO_COORD[get_move_target!(BEST_MOVE) as usize],
            ASCII_PIECES[get_move_promoted!(BEST_MOVE) as usize]
            );
        }else {
            println!("bestmove {}{}",
            SQUARE_TO_COORD[get_move_source!(BEST_MOVE) as usize],
            SQUARE_TO_COORD[get_move_target!(BEST_MOVE) as usize],
            );
        }
    }
}

fn score_move(mv: u64) -> usize {
    unsafe {
        // if PV move scoring is enabled 
        if SCORE_PV != 0 {
            // make sure we are dealing with the PV move
            if PV_TABLE[0][PLY] == mv {
                SCORE_PV = 0;

                return 20000;
            }
        }

        if get_move_capture!(mv) != 0 {

            let mut target_piece = 0;
            let mut start_piece = 0;
            let mut end_piece = 0;

            if SIDE == PieceColor::WHITE as i32 {
                start_piece = Piece::p as usize;
                end_piece = Piece::k as usize;
            }else {
                start_piece = Piece::P as usize;
                end_piece = Piece::K as usize;
            }

            for bb_piece in start_piece..=end_piece {
                if get_bit!(PIECE_BITBOARDS[bb_piece], get_move_target!(mv)) != 0 {
                    target_piece = bb_piece;
                    break;
                }
            }

            return MVV_LVA[get_move_piece!(mv) as usize][target_piece] +10000;


        }else {
            // score 1st killer move
            if KILLER_MOVES[0][PLY] == mv as usize {
                return 9000;
            // score 2nd killer move
            }else if KILLER_MOVES[1][PLY] == mv as usize {
                return 8000;
            // score history move
            }else {
                return HISTORY_MOVES[get_move_piece!(mv) as usize][get_move_target!(mv) as usize];
            }
        }
    }
    
}


fn enable_pv_scoring(move_list: &Vec<u64>) {
    unsafe {
        // disable following PV
        FOLLOW_PV = 0;

        for mv in move_list {
            // make sure we hit PV move
            if PV_TABLE[0][PLY] == *mv {
                // enable move scoring
                SCORE_PV = 1;

                // enable following PV
                FOLLOW_PV = 1;
            }
        }

    }
}

fn evaluate() -> i32 {
    let mut score = 0;

    let mut bitboard: u64 = 0;

    //let mut piece = 0;

    let mut square = 0;

    for bb_piece in Piece::P as usize..=Piece::k as usize {
        unsafe {
            bitboard = PIECE_BITBOARDS[bb_piece];

            while bitboard != 0 {
                //piece = bb_piece;

                square = match index_lsb(bitboard) {
                    Ok(val) => val,
                    Err(_) => panic!(),
                };
                
                // score material weights
                score += MATERIAL_SCORE[bb_piece];

                // score positional piece scores
                match bb_piece {
                    // evaluate white pieces
                    0 => score += PAWN_SCORE[square],
                    1 => score += KNIGHT_SCORE[square],
                    2 => score += BISHOP_SCORE[square],
                    3 => score += ROOK_SCORE[square],
                    5 => score += KING_SCORE[square],

                    // evaluate Black pieces
                    6 => score -= PAWN_SCORE[MIRROR_SCORE[square]],
                    7 => score -= KNIGHT_SCORE[MIRROR_SCORE[square]],
                    8 => score -= BISHOP_SCORE[MIRROR_SCORE[square]],
                    9 => score -= ROOK_SCORE[MIRROR_SCORE[square]],
                    11 => score -= KING_SCORE[MIRROR_SCORE[square]],

                    _ => {},
                }

                reset_bit!(bitboard, square);
            }
        }
    }

    unsafe {
        if SIDE == PieceColor::WHITE as i32 {
            score 
        }else {
            -score 
        }
    }

}

fn sort_moves(move_list: &mut Vec<u64>) {

    let mut move_scores = move_list.clone().iter().map(|x| score_move(*x)).collect::<Vec<usize>>();

    for current_move in 0..move_list.len() {
        for next_move in current_move+1..move_list.len() {
            if move_scores[current_move] < move_scores[next_move] {
                move_list.swap(current_move, next_move);
                move_scores.swap(current_move, next_move);
            }
        }
    }
}

fn quiescence(mut alpha: i32, beta: i32) -> i32 {

    unsafe{
    // every 2047 nodes
    if (NODES % 2047) == 0{
        communicate();
    }
    // increment nodes count
    NODES += 1;

    // evaluate position
    let evaluation = evaluate();

    // fail-hard beta cutoff
    if evaluation >= beta {
        // node (move) fails high
        return beta;
    }

    // found a better move
    if evaluation > alpha {
        // PV node (move)
        alpha = evaluation;
    }

    let mut legal_moves = generate_moves();

    legal_moves.sort_by_key(|&x|  std::cmp::Reverse(score_move(x)));

    //sort_moves(&mut legal_moves);

    for mv in legal_moves.iter() {
        // preserve board state
        let (piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy) = copy_board();

        // increment ply
        PLY += 1;

        if !make_move(*mv, MOVE_TYPE::only_captures) {
            PLY -= 1;
            continue;
        }

        let score = -quiescence(-beta, -alpha);

        PLY-= 1;

        take_back(piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy);

        if STOPPED == 1 {
            return 0;
        }

        // fail-hard beta cutoff
        if score >= beta {
            // node (move) fails high
            return beta;
        }

        // found a better move
        if score > alpha {
            alpha = score;
        }
    }
    return alpha;
    }
    
}


// negamax alpha beta search
fn negamax(mut alpha: i32, beta: i32, mut depth: usize) -> i32 {
    unsafe {
        // // every 2047 nodes
        if (NODES % 2047) == 0 {
            communicate();
        }

        // define find PV node variable
        let mut found_pv = false;

        // init PV length
        PV_LENGTH[PLY] = PLY as u64;

        if depth == 0 {
            // run quiescence search
            return quiescence(alpha, beta);

        }else {
            // Check if PLY reached the maximum ply allowed by PV_LENGTH and PV_TABLE
            if PLY > 63 {
                return evaluate();
            }

            NODES += 1;

            let mut best_sofar: u64 = 0;

            let old_alpha = alpha;

            let mut in_check: bool = false;

            if SIDE == PieceColor::WHITE as i32 {
                let king_square = match index_lsb(PIECE_BITBOARDS[Piece::K as usize]){
                    Ok(val) => val as u64,
                    Err(e) => panic!("error: {:?}", e),
                };

                in_check = is_square_attacked(king_square, PieceColor::BLACK as u64);
            }else {
                let king_square = match index_lsb(PIECE_BITBOARDS[Piece::k as usize]){
                    Ok(val) => val as u64,
                    Err(e) => panic!("error: {:?}", e),
                };

                in_check = is_square_attacked(king_square, PieceColor::WHITE as u64);
            }

            if in_check {
                depth += 1;
            }   

            // null move pruning
            if depth >= 3 && !in_check && PLY != 0 {
                let (piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy) = copy_board();

                SIDE ^= 1;

                ENPASSANT = BoardSquare::no_sq as u32;

                let score = -negamax(-beta, -beta+1, depth-1-2);

                take_back(piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy);

                if score >= beta {
                    return beta;
                }
            }


            let mut legal_moves = generate_moves();

            // if we are following principle variation line
            if FOLLOW_PV != 0 {
                // enable PV move scoring
                enable_pv_scoring(&legal_moves);
            }

            legal_moves.sort_by_key(|&x|  std::cmp::Reverse(score_move(x)));

            let mut moves_searched = 0;


            for mv in legal_moves.iter() {
                let (piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy) = copy_board();

                PLY += 1;

                make_move(*mv, MOVE_TYPE::all_moves);

                let mut score = 0;
                // if we hit PV node 
                if moves_searched == 0 {

                    score = -negamax(-beta, -alpha, depth - 1);
                    
                }else{
                    // full depth search
                    
                    // conditions to consider LMR
                    if moves_searched >= FULL_DEPTH_MOVE 
                    && depth >= REDUCTION_LIMIT 
                    && in_check == false
                    && get_move_capture!(*mv) == 0 
                    && get_move_promoted!(*mv) == 0 
                    {
                        score = -negamax(-alpha - 1, -alpha, depth - 2);

                    }else{
                        // hack to ensure that full-depth search is done
                        score = alpha +1;
                    }
                    // principle variation search PVS
                    if score > alpha {
                        // /* Once you've found a move with a score that is between alpha and beta,
                        // the rest of the moves are searched with the goal of proving that they are all bad.
                        // It's possible to do this a bit faster than a search that worries that one
                        // of the remaining moves might be good. */
                        score = -negamax(-alpha - 1, -alpha, depth-1);

                        // /* If the algorithm finds out that it was wrong, and that one of the
                        // subsequent moves was better than the first PV move, it has to search again,
                        // in the normal alpha-beta manner.  This happens sometimes, and it's a waste of time,
                        // but generally not often enough to counteract the savings gained from doing the
                        // "bad move proof" search referred to earlier. */
                        if score > alpha && score < beta {
                            score = -negamax(-beta, -alpha, depth-1);
                        }
                    }
                    
                }

                PLY -=1;

                take_back(piece_bitboards_copy, occupancies_copy, side_copy, enpassant_copy, castle_copy);

                if STOPPED == 1 {
                    return 0;
                }
                

                moves_searched += 1;

                // fail-hard beta cutoff
                if score >= beta {
                    // on quiet moves
                    if get_move_capture!(*mv) == 0 {
                        // store killer moves
                        KILLER_MOVES[1][PLY] = KILLER_MOVES[0][PLY];
                        KILLER_MOVES[0][PLY] = *mv as usize;
                    } 

                    
                    return beta;
                }

                // found a better move
                if score > alpha {
                    // on quiet moves
                    if get_move_capture!(*mv) == 0 {
                        // store history moves
                        HISTORY_MOVES[get_move_piece!(*mv) as usize][get_move_target!(*mv) as usize] += depth;
                    }
                    
                    // PV node (move)
                    alpha = score;

                    // enable found pv flag
                    found_pv = true;

                    // write PV move
                    PV_TABLE[PLY][PLY] = *mv;

                    // loop over the next ply
                    for next_ply in PLY +1 .. PV_LENGTH[PLY +1] as usize {
                        // copy move from deeper ply into a current ply's line
                        PV_TABLE[PLY][next_ply] = PV_TABLE[PLY+1][next_ply];
                    }

                    // adjust PV length
                    PV_LENGTH[PLY] = PV_LENGTH[PLY+1];

                    if PLY == 0 {
                        // associate best move with the best score
                        best_sofar = *mv;
                    }
                }

                
            }

            // detecting checkmate and stalemate
            if legal_moves.len() == 0 {
                if in_check {
                    return -49000 + PLY as i32;
                }else {
                    return 0;
                }
            }

            // found better move
            if old_alpha != alpha {
                BEST_MOVE = best_sofar;

            }

            return alpha;
        }
    }
}

// parse UCI "go" command
fn parse_go(command: String) {

    unsafe {
        QUIT = 0;
        MOVESTOGO = 30;
        MOVETIME = -1;
        TIME= -1;
        INC = 0;
        STARTTIME = 0;
        STOPTIME = 0;
        TIMESET= 0;
        STOPPED= 0;
    }

    let mut depth = -1;

    if command.chars().skip(3).take(5).collect::<Vec<char>>().iter().collect::<String>() == "depth" {
        let current_depth = command.chars().skip(9).collect::<Vec<char>>().iter().collect::<String>();

        if current_depth.chars().count() > 0 {
            depth = match current_depth.parse::<usize>() {
                Ok(val) => val as i32,
                Err(e) => panic!("unknown value for depth: {}", e),
            };
        }
    // infinite search
    }
    if command.chars().skip(3).take(8).collect::<Vec<char>>().iter().collect::<String>() == "infinite"{

    }if command.chars().skip(3).take(5).collect::<Vec<char>>().iter().collect::<String>() == "wtime" {
        let mut time_controls = command.chars().skip(3).collect::<Vec<char>>().iter().collect::<String>();
        time_controls = time_controls.trim().to_string();

        let time_controls = time_controls.split(" ").collect::<Vec<&str>>();

        if time_controls.len() >= 2 {
            let wtime = match time_controls[1].parse::<usize>() {
                Ok(val) => val,
                Err(e) => panic!("unknown value for wtime: {}", e),
            };
    
            unsafe {
                if SIDE == PieceColor::WHITE as i32 {
                    TIME = wtime as i64;
                }   
            }
        }
        
        if time_controls.len() >= 4 {
            let btime = match time_controls[3].parse::<usize>() {
                Ok(val) => val,
                Err(e) => panic!("unknown value for btime: {}", e),
            };
    
            unsafe {
                if SIDE == PieceColor::BLACK as i32 {
                    TIME = btime as i64;
                }
                
            }
        }
        
        if time_controls.len() >= 6 {
            let winc = match time_controls[5].parse::<usize>() {
                Ok(val) => val,
                Err(e) => panic!("unknown value for winc: {}", e),
            };
    
            unsafe {
                if SIDE == PieceColor::WHITE as i32 {
                    INC = winc as i64;
                }
                
            }
        }
        
        if time_controls.len() >= 8 {
            let binc = match time_controls[7].parse::<usize>() {
                Ok(val) => val,
                Err(e) => panic!("unknown value for binc: {}", e),
            };
    
            unsafe {
                if SIDE == PieceColor::BLACK as i32 {
                    INC = binc as i64;
                }
                
            }
        }
        


    }

    if command.chars().skip(3).take(9).collect::<Vec<char>>().iter().collect::<String>() == "movestogo" {
        let movestogo = command.chars().skip(13).collect::<Vec<char>>().iter().collect::<String>();

        let movestogo = match movestogo.parse::<usize>() {
            Ok(val) => val,
            Err(e) => panic!("unknown value for movestogo: {}", e),
        };

        unsafe {
            MOVESTOGO = movestogo as u64;
        }
    }

    if command.chars().skip(3).take(8).collect::<Vec<char>>().iter().collect::<String>() == "movetime" {
        let movetime= command.chars().skip(12).collect::<Vec<char>>().iter().collect::<String>();

        let movetime = match movetime.parse::<usize>() {
            Ok(val) => val,
            Err(e) => panic!("unknown value for movetime: {}", e),
        };

        unsafe {
            MOVETIME = movetime as i64;
        }

    }

    unsafe {
        if MOVETIME !=-1 {
            TIME= MOVETIME;
            MOVESTOGO= 1;
        }

        STARTTIME = get_time_ms() as u64;

        if TIME!= -1 {
            TIMESET = 1;

            TIME /= MOVESTOGO as i64;
            TIME -= 50;
            STOPTIME = STARTTIME + TIME as u64 + INC as u64;
        }
    }

    if depth == -1 {
        depth = 64;
    }
    unsafe {
        println!("time:{} start:{} stop:{} depth:{} timeset:{}", TIME, STARTTIME, STOPTIME, depth, TIMESET);
    }
    
    search_position(depth as usize);

}

fn uci_loop(char_pieces: &HashMap<char, u32>) {
    println!("id name cheng");
    println!("id author Ramez Essam");
    println!("uciok");
    let mut input = String::new();
    
    loop {
        io::stdout().flush().unwrap();
        // read input from stdin
        io::stdin().read_line(&mut input).expect("failed to read line");
        input = input.trim().to_string();

        if input == "isready" {
            println!("readyok");
        }else if input.chars().take(8).collect::<Vec<char>>().iter().collect::<String>() == "position" {
            parse_position(input.clone(), char_pieces);
        }else if input.chars().take(10).collect::<Vec<char>>().iter().collect::<String>() == "ucinewgame" {
            parse_position("position startpos".to_string(), char_pieces);
        }else if input.chars().take(2).collect::<Vec<char>>().iter().collect::<String>() == "go" {
            parse_go(input.clone());
        }else if input.chars().take(4).collect::<Vec<char>>().iter().collect::<String>() == "quit" {
            break;
        }else if input.chars().take(3).collect::<Vec<char>>().iter().collect::<String>() == "uci" {
            println!("id name cheng");
            println!("id author Ramez Essam");
            println!("uciok");
        }else if input.chars().take(1).collect::<Vec<char>>().iter().collect::<String>() == "d" {
            print_board();
        }else if input.chars().take(8).collect::<Vec<char>>().iter().collect::<String>() == "evaluate" {
            println!("static evaluation: {}", evaluate());
        }

        input.clear();


    }
}



fn main() {

    let mut char_pieces: HashMap<char, u32> = HashMap::new();

    init_char_pieces(&mut char_pieces);

    init_leaper_table();

    init_sliders_table(1);
    init_sliders_table(0);

    uci_loop(&char_pieces);

    // parse_fen(START_POSTITION, &char_pieces);
    


    // print_board();

    // parse_position("position startpos moves e2e4 b8c6 b1c3 e7e5".to_string(), &char_pieces);

    // print_board();

    // parse_go("go wtime 280447 btime 280432 winc 2000 binc 2000".to_string())
    

    

}
