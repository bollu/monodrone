use egui::*;

pub const BOX_DIM : Vec2 = Vec2::new(25., 25.);
pub const BOX_PADDING_MIN : Vec2 = Vec2::new(3., 3.);
pub const BOX_PADDING_MAX : Vec2 = Vec2::new(3., 3.);
pub const WINDOW_PADDING : Vec2 = Vec2::new(10.0, BOX_PADDING_MIN.y);
pub const SIDEBAR_LEFT_WIDTH : f32 = 15.0;
pub const BOX_DESELECTED_COLOR : egui::Color32 = egui::Color32::from_rgb(66, 66, 66);
pub const BOX_CURSORED_COLOR : egui::Color32 = egui::Color32::from_rgb(189, 189, 189);
pub const BOX_CURSOR_COLOR : egui::Color32 = egui::Color32::from_rgb(250, 250, 250);
pub const BOX_NOW_PLAYING_COLOR : egui::Color32 = egui::Color32::from_rgb(255, 143, 0);
pub const TEXT_COLOR_LEADING : egui::Color32 = egui::Color32::from_rgb(207, 216, 220);
pub const TEXT_COLOR_FOLLOWING : egui::Color32 = egui::Color32::from_rgb(99, 99, 99);
pub const FONT_SIZE_NOTE : f32 = 10.0;
pub const FONT_SIZE_OCTAVE : f32 = 10.0;
pub const NTRACKS : u64 = 4;
pub const TRACK_LENGTH : u64 = 100;
pub const NUM_HISTORY_STEPS : usize = 10000;