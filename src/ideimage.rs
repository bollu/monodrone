#![allow(rustdoc::missing_crate_level_docs)] // it's an example
#![allow(dead_code)]



use serde::{Deserialize, Serialize};
 // 0.7.2
use tracing_subscriber::fmt::MakeWriter;

use std::path::PathBuf;

use std::time::Duration;
use std::{fs::File};

use eframe::egui;
use egui::*;



use tracing::{event, Level};


use crate::*;

fn audio_dir() -> PathBuf {
    let mut out = directories::UserDirs::new().unwrap().audio_dir().unwrap().to_path_buf();
    out.push("Monodrone");
    std::fs::create_dir_all(&out).unwrap();
    out
}

fn ide_image_file_path() -> PathBuf {
    let mut out = audio_dir();
    let filename = "monodrone-settings.json";
    out.push(filename);
    out
}


// The image file, that has all the state.  #[derive(Debug, Serialize, Deserialize)]
#[derive(Debug, Serialize, Deserialize)]
pub struct IDEImage {
    contexts : Vec<Project>,
    last_modified : LastModified,
    ix : i32,
}


fn save_project(ctx : &Project) {
    // let midi_filepath = dir ctx.get_midi_export_file_path();
    let mut path = audio_dir();
    path.push(format!("{}.mid", ctx.track_name.clone()));

    let midi_file = match File::create(path.clone()) {
        Ok(file) => file,
        Err(e) => {
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title("Unable to create MIDI file")
                .set_description(e.to_string())
                .show();
            event!(Level::ERROR, "error creating MIDI file: {:?}", e);
            return;
        }
    };
    let (header, tracks) = ctx.to_smf();
    match midly::write_std(&header, tracks.iter(), midi_file) {
        Ok(()) => {
            event!(Level::INFO, "Successfully saved MIDI file '{}'", path.to_string_lossy());
        }
        Err(e) => {
            rfd::MessageDialog::new()
                .set_level(rfd::MessageLevel::Error)
                .set_title("Unable to save MIDI file")
                .set_description(e.to_string())
                .show();
            event!(Level::ERROR, "error writing MIDI file: {:?}", e);
        }
    }
}


impl IDEImage {
    pub fn ctx_mut(&mut self) -> &mut Project {
        &mut self.contexts[self.ix as usize]
    }

    // TODO: rename ctx to ctx_mut.
    pub fn ctx(&self) -> &Project {
        &self.contexts[self.ix as usize]
    }

    pub fn load() -> Self {
        let mut default =
            IDEImage {
                contexts : vec![Project::new("track-0".to_string())],
                ix : 0,
                last_modified : LastModified::new(),
            };
        let path = ide_image_file_path();
        let file =
            match File::open(path.clone()) {
                Ok(file) => {
                    event!(Level::INFO, "opened settings fil at '{}'", path.to_string_lossy());
                    file
                }
                Err(err) => {
                    event!(Level::ERROR, "error loading settings file at '{}': {:?}", path.to_string_lossy(), err);
                    default.save();
                    return default
                }
            };

        let reader = std::io::BufReader::new(file);
        match ron::de::from_reader(reader) {
            Ok(settings) => {
                event!(Level::INFO, "loaded settings from file: {:?}", path);
                settings
            }
            Err(err) => {
                event!(Level::ERROR, "failed to load settings file: '{:?}'", err);
                default.save();
                default
            }
        }
    }

    pub fn new(&mut self) {
        let ix = self.contexts.len();
        let ctx = Project::new(format!("track-{}", ix));
        self.contexts.push(ctx);
        self.ix = ix as i32;
    }

    // save the settings to the settings file.
    pub fn save(&mut self) {
        for ctx in &mut self.contexts {
            // TODO: make this a trait.
            self.last_modified.union(&ctx.last_modified);
        }

        // only save if we are both (a) dirty, and (b) have been idle for X seconds.
        if !self.last_modified.is_dirty_and_idle_for(Duration::from_secs(1)) {
            return;
        }
        self.last_modified.clean();

        let path = ide_image_file_path();
        match File::create(path.clone()) {
            Ok(file) => {
                let writer = file.make_writer();
                ron::ser::to_writer(writer, &self).unwrap();
                event!(Level::INFO, "Successfully saved settings file to path {:?}", path.to_string_lossy());
            }
            Err(e) => {
                event!(Level::ERROR, "Error saving settings file '{}': {:?}", path.to_string_lossy(),
                    e);
            }
        }
        save_project(self.ctx());
    }

    pub fn switch_to(&mut self, ix: i32) {
        assert!(ix < self.contexts.len() as i32);
        assert!(ix >= 0);
        self.ix = ix;
    }
}


pub fn egui_project_picker(_ctx : &egui::Context, ui: &mut egui::Ui, settings : &mut IDEImage) {
    ui.with_layout(Layout::top_down_justified(Align::Min), |ui| {
        let mut selected_ix : i32 = settings.ix ;
        for (i, ctx) in settings.contexts.iter().enumerate() {
            if ui.selectable_label(i == settings.ix as usize, ctx.track_name.clone()).clicked() {
                selected_ix = i as i32;
            }
        }

        settings.switch_to(selected_ix);
    });
}
