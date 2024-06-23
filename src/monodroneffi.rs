
use std::collections::HashMap;
use lean_sys::{lean_io_mark_end_initialization, lean_initialize_runtime_module, lean_box, lean_inc_ref, lean_object};

extern {
    pub fn initialize_Monodrone(builtin : u8, world : *mut lean_object) -> lean_object;

    // ctx.
    fn monodrone_ctx_new (unit : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_step (ctx : *mut lean_object) -> *mut lean_object;

    // cursor movement.
    fn monodrone_ctx_cursor_move_left_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_cursor_move_right_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_cursor_move_down_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_cursor_move_up_one(ctx: *mut lean_object) -> *mut lean_object;

    // selection movement.
    fn monodrone_ctx_select_anchor_move_left_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_select_anchor_move_right_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_select_anchor_move_down_one(ctx: *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_select_anchor_move_up_one(ctx: *mut lean_object) -> *mut lean_object;
    // note editing.
    fn monodrone_ctx_set_pitch(ctx : *mut lean_object, pitch : u64) -> *mut lean_object;
    fn monodrone_ctx_delete(ctx : *mut lean_object) -> *mut lean_object;
    // fn monodrone_ctx_toggle_note_sharp(ctx : *mut lean_object);
    // fn monodrone_ctx_toggle_note_flat(ctx : *mut lean_object);
    fn monodrone_ctx_increase_duration(ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_decrease_duration(ctx : *mut lean_object) -> *mut lean_object;
    // fn monodrone_goto_end_of_line(ctx : *mut lean_object);
    // fn monodrone_goto_begin_of_line(ctx : *mut lean_object);
    // fn monodrone_copy(ctx : *mut lean_object);
    // fn monodrone_paste(ctx : *mut lean_object);


    // cursor query
    fn monodrone_ctx_get_cursor_sync_index(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_cursor_x(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_cursor_y(ctx : *mut lean_object) -> u64;

    // selection query
    // fn monodrone_ctx_has_select_anchor (ctx : *mut lean_object) -> bool;
    fn monodrone_ctx_get_select_anchor_x (ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_select_anchor_y (ctx : *mut lean_object) -> u64;


    // track query
    fn monodrone_ctx_get_track_sync_index(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_track_length(ctx : *mut lean_object) -> u64;
    fn monodrone_ctx_get_track_note(ctx : *mut lean_object, i : u64) -> *mut lean_object;

    // note query
    fn monodrone_note_get_pitch_name(note : *mut lean_object) -> u64;
    // fn monodrone_note_get_accidental(note : *mut lean_object) -> u64;
    fn monodrone_note_get_x(note : *mut lean_object) -> u64;
    fn monodrone_note_get_y(note : *mut lean_object) -> u64;
    fn monodrone_note_get_nsteps(note : *mut lean_object) -> u64;

    // Undo/Redo action
    fn monodrone_ctx_undo_action(ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_redo_action(ctx : *mut lean_object) -> *mut lean_object;

    // Undo/Redo movement
    fn monodrone_ctx_undo_movement (ctx : *mut lean_object) -> *mut lean_object;
    fn monodrone_ctx_redo_movement (ctx : *mut lean_object) -> *mut lean_object;

}

/// Run a function that is linear in the monodrone ctx, so we bump the ref count once and then call the function.
pub fn monodrone_ctx_run_linear_fn<T> (ctx : *mut lean_object, f : unsafe extern "C" fn(*mut lean_object) -> T) -> T {
    unsafe {
        lean_inc_ref(ctx);
        f(ctx)
    }
}

// # Ctx function wrappers.
pub fn initialize() -> () {
    unsafe { initialize_Monodrone(1, lean_box(0)) };
}
pub fn new_context() -> *mut lean_object {
    unsafe { monodrone_ctx_new(lean_box(0)) }
}

// cursor movement.
pub fn cursor_move_left_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_left_one) }

}
pub fn cursor_move_right_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_right_one) }
}
pub fn cursor_move_down_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_down_one) }
}
pub fn cursor_move_up_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_cursor_move_up_one) }
}

pub fn select_anchor_move_left_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_left_one) }
}

pub fn select_anchor_move_right_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_right_one) }
}

pub fn select_anchor_move_down_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_down_one) }
}

pub fn select_anchor_move_up_one(ctx: *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_select_anchor_move_up_one) }
}

// note editing.
pub fn set_pitch(ctx : *mut lean_object, pitch : PitchName) -> *mut lean_object {
    unsafe { lean_inc_ref(ctx); }
    unsafe { monodrone_ctx_set_pitch(ctx, pitch.to_lean() ) }
}

pub fn delete(ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_delete) }

}
pub fn increase_duration(ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_increase_duration) }
}

pub fn decrease_duration(ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_decrease_duration) }
}


pub fn get_track_sync_index (ctx : *mut lean_object) -> u64 {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_track_sync_index) }
}

pub fn get_cursor_sync_index (ctx : *mut lean_object) -> u64 {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_sync_index) }
}




pub fn step (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_step) }
}

pub fn undo_action (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_undo_action) }
}

pub fn redo_action (ctx : *mut lean_object) -> *mut lean_object {
    unsafe { monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_redo_action) }
}



#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PlayerNote {
    pub pitch: u64,
    pub start: u64,
    pub nsteps: u64,
}


#[derive(Debug, Clone, PartialEq)]
pub struct PlayerTrack {
    pub notes: Vec<PlayerNote>, // sorted by start
}

impl PlayerTrack {
    pub fn new() -> PlayerTrack {
        PlayerTrack { notes: Vec::new() }
    }

}

#[derive(Debug, Clone, PartialEq)]
pub struct TrackBuilder {
    notes: Vec<PlayerNote>,
    time : u64,
}
impl TrackBuilder {
    pub fn new() -> TrackBuilder {
        TrackBuilder { notes: Vec::new(), time: 0 }
    }

    /// Add a note to the track that is held for `nsteps` steps.
    pub fn note_held(&mut self, pitch: u64, nsteps: u64) -> &mut Self {
        self.notes.push(PlayerNote { pitch, start: self.time, nsteps });
        self.time += nsteps;
        self
    }

    /// Add a note to the track that is held for 1 step.
    pub fn note1(&mut self, pitch: u64) -> &mut Self {
        self.note_held(pitch, 1)
    }

    /// Add a note to the track that is held for 1 step.
    pub fn note8(&mut self, pitch: u64) -> &mut Self {
        self.note_held(pitch, 8)
    }


    /// Add a rest to the track of `nsteps` steps.
    pub fn rest(&mut self, nsteps: u64) -> &mut Self {
        self.time += nsteps;
        self
    }

    pub fn build(&self) -> PlayerTrack {
        PlayerTrack { notes: self.notes.clone() }
    }
}


impl From<TrackBuilder> for PlayerTrack {
    fn from(builder: TrackBuilder) -> Self {
        PlayerTrack { notes: builder.notes }
    }
}



#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PitchName {
    C,
    D,
    E,
    F,
    G,
    A,
    B,
}

impl PitchName {
    pub fn to_str(&self) -> &str {
        match self {
            PitchName::C => "C",
            PitchName::D => "D",
            PitchName::E => "E",
            PitchName::F => "F",
            PitchName::G => "G",
            PitchName::A => "A",
            PitchName::B => "B",
        }
    }

    pub fn to_lean(&self) -> u64 {
        match self {
            PitchName::C => 0,
            PitchName::D => 1,
            PitchName::E => 2,
            PitchName::F => 3,
            PitchName::G => 4,
            PitchName::A => 5,
            PitchName::B => 6,
        }
    }

    pub fn of_lean (ix : u64) -> PitchName {
        match ix {
            0 => PitchName::C,
            1 => PitchName::D,
            2 => PitchName::E,
            3 => PitchName::F,
            4 => PitchName::G,
            5 => PitchName::A,
            6 => PitchName::B,
            _ => panic!("Invalid pitch name index {}", ix),
        }
    }

}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Accidental {
    Natural,
    Sharp,
    Flat,
}

impl Accidental {
    pub fn to_str(&self) -> &str {
        match self {
            Accidental::Natural => "",
            Accidental::Sharp => "#",
            Accidental::Flat => "b",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct UINote {
    pub pitchName: PitchName,
    pub accidental : Accidental,
    pub x: u64,
    pub y: u64,
    pub nsteps: u64,

}

impl UINote {
    pub fn to_str (&self) -> String {
        format!("{}{}", self.pitchName.to_str(), self.accidental.to_str())
    }
}

fn pitch_name_to_midi_pitch (pitchName : PitchName) -> u64 {
    match pitchName {
        PitchName::C => 60,
        PitchName::D => 62,
        PitchName::E => 63,
        PitchName::F => 64,
        PitchName::G => 66,
        PitchName::A => 68,
        PitchName::B => 70,
    }
}

fn accidental_to_midi_pitch (accidental : Accidental) -> i64 {
    match accidental {
        Accidental::Natural => 0,
        Accidental::Sharp => 1,
        Accidental::Flat => -1,
    }
}

fn ui_pitch_to_midi_pitch (pitchName : PitchName, accidental : Accidental) -> u64 {
    (pitch_name_to_midi_pitch(pitchName) as i64 + accidental_to_midi_pitch(accidental)) as u64
}

impl UINote {
    pub fn from_lean (note : *mut lean_object) -> UINote {
        let pitchName = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_pitch_name) };
        let x = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_x) };
        let y = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_y) };
        let nsteps = unsafe { monodrone_ctx_run_linear_fn(note, monodrone_note_get_nsteps) };
        UINote { pitchName: PitchName::of_lean(pitchName), accidental: Accidental::Natural, x, y, nsteps }
    }

    pub fn to_player_note (&self) -> PlayerNote {
        PlayerNote { pitch: ui_pitch_to_midi_pitch(self.pitchName, self.accidental) ,
            start: self.y, nsteps: self.nsteps }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UITrack {
    pub sync_index: u64,
    pub notes: Vec<UINote>,
    pub hitbox : HashMap<(u64, u64), usize>, // maps (x, y) to index in notes.
}

impl UITrack {
    pub fn from_lean (ctx : *mut lean_object) -> UITrack {
        let len: u64 = unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_track_length)
        };
        let mut notes: Vec<UINote> = Vec::new();
        for i in 0..len {
            unsafe {
                lean_inc_ref(ctx);
                let note  = monodrone_ctx_get_track_note(ctx, i);
                notes.push(UINote::from_lean(note));
            }
        }

        let mut hitbox = HashMap::new();
        for (ix, note) in notes.iter().enumerate() {
            for y in note.y..note.y + note.nsteps {
                hitbox.insert((note.x, y), ix);
            }
        }

        let sync_index = unsafe {
            monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_track_sync_index)
        };

        UITrack { sync_index, notes, hitbox }
    }

    pub fn get_note_from_coord (&self, x : u64, y : u64) -> Option<&UINote> {
        match self.hitbox.get(&(x, y)) {
            Some(ix) => Some(&self.notes[*ix]),
            None => None,
        }
    }

    pub fn to_player_track (&self) -> PlayerTrack {
        let mut notes = Vec::new();
        for note in &self.notes {
            notes.push(note.to_player_note());
        }
        PlayerTrack { notes }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Selection {
    pub sync_index: u64,
    pub anchor_x: u64,
    pub anchor_y: u64,
    pub cursor_x: u64,
    pub cursor_y: u64,
}

impl Selection {
    pub fn from_lean (ctx : *mut lean_object) -> Selection {
        Selection {
            sync_index: unsafe {
                monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_sync_index)
             },
            anchor_x: unsafe {
                monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_select_anchor_x)
             },
            anchor_y: unsafe {
                monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_select_anchor_y)
             },
            cursor_x: unsafe {
                monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_x)
             },
            cursor_y: unsafe {
                monodrone_ctx_run_linear_fn(ctx, monodrone_ctx_get_cursor_y)
             },
        }
    }

    pub fn is_cursored(&self, x: u64, y: u64) -> bool {
        self.cursor_x == x && self.cursor_y == y
    }

    pub fn is_selected (&self, x : u64, y : u64) -> bool {
        let min_x = self.anchor_x.min(self.cursor_x);
        let max_x = self.anchor_x.max(self.cursor_x);
        let min_y = self.anchor_y.min(self.cursor_y);
        let max_y = self.anchor_y.max(self.cursor_y);
        x >= min_x && x <= max_x && y >= min_y && y <= max_y
    }
}
