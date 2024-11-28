use raugeas_sys::*;

bitflags! {
    /// Flag to be passed to the `Augeas::init` method.
    pub struct Flags: aug_flags {
        /// No flags
        const NONE = aug_flags_AUG_NONE;
        /// Keep the original file with a `.augsave` extension
        const SAVE_BACKUP = aug_flags_AUG_SAVE_BACKUP;
        /// Save changes into a file with extension `.augnew`, and do not
        ///  overwrite the original file. Takes precedence over `SAVE_BACKUP`.
        const SAVE_NEW_FILE = aug_flags_AUG_SAVE_NEWFILE;
        /// Typecheck lenses. Since it can be very expensive it is not done by default.
        const TYPE_CHECK = aug_flags_AUG_TYPE_CHECK;
        /// Do not use the builtin load path for modules.
        const NO_STD_INCLUDE = aug_flags_AUG_NO_STDINC;
        /// Make save a no-op process, just record what would have changed.
        const SAVE_NOOP = aug_flags_AUG_SAVE_NOOP;
        /// Do not load the tree from `init`.
        const NO_LOAD = aug_flags_AUG_NO_LOAD;
        /// Do not load the tree nor any lenses.
        const NO_MODULE_AUTOLOAD = aug_flags_AUG_NO_MODL_AUTOLOAD;
        /// Track the span in the input of nodes.
        const ENABLE_SPAN = aug_flags_AUG_ENABLE_SPAN;
        /// Do not close automatically when encountering error during `init`.
        const NO_ERROR_CLOSE = aug_flags_AUG_NO_ERR_CLOSE;
        /// Print a trace of the modules that are being loaded.
        const TRACE_MODULE_LOADING = aug_flags_AUG_TRACE_MODULE_LOADING;
    }
}
