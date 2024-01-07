use rustc_data_structures::fx::{FxHashMap, FxIndexSet};
use rustc_data_structures::sync::Lrc;
use rustc_middle::mir::interpret::{self, AllocDecodingState, AllocId};
use rustc_middle::ty::{self, Ty, TyCtxt, TyDecoder, TyEncoder};
use rustc_serialize::opaque::MemDecoder;
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_session::StableCrateId;
use rustc_span::def_id::{CrateNum, DefId, DefIndex};
use rustc_span::{
    BytePos, SourceFile, Span, SpanDecoder, SpanEncoder, StableSourceFileId, Symbol, SyntaxContext,
    DUMMY_SP,
};

// This is the last available version of `MemEncoder` in rustc_serialize::opaque before its removal.
pub struct MemEncoder {
    pub data: Vec<u8>,
}

impl MemEncoder {
    pub fn new() -> MemEncoder {
        MemEncoder { data: vec![] }
    }

    #[inline]
    pub fn position(&self) -> usize {
        self.data.len()
    }

    pub fn finish(self) -> Vec<u8> {
        self.data
    }
}

macro_rules! write_leb128 {
    ($enc:expr, $value:expr, $int_ty:ty, $fun:ident) => {{
        const MAX_ENCODED_LEN: usize = rustc_serialize::leb128::max_leb128_len::<$int_ty>();
        let mut buf = [0; MAX_ENCODED_LEN];
        let encoded = rustc_serialize::leb128::$fun(&mut buf, $value);
        $enc.data.extend_from_slice(&buf[..encoded]);
    }};
}

impl Encoder for MemEncoder {
    #[inline]
    fn emit_usize(&mut self, v: usize) {
        write_leb128!(self, v, usize, write_usize_leb128)
    }

    #[inline]
    fn emit_u128(&mut self, v: u128) {
        write_leb128!(self, v, u128, write_u128_leb128);
    }

    #[inline]
    fn emit_u64(&mut self, v: u64) {
        write_leb128!(self, v, u64, write_u64_leb128);
    }

    #[inline]
    fn emit_u32(&mut self, v: u32) {
        write_leb128!(self, v, u32, write_u32_leb128);
    }

    #[inline]
    fn emit_u16(&mut self, v: u16) {
        self.data.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn emit_u8(&mut self, v: u8) {
        self.data.push(v);
    }

    #[inline]
    fn emit_isize(&mut self, v: isize) {
        write_leb128!(self, v, isize, write_isize_leb128)
    }

    #[inline]
    fn emit_i128(&mut self, v: i128) {
        write_leb128!(self, v, i128, write_i128_leb128)
    }

    #[inline]
    fn emit_i64(&mut self, v: i64) {
        write_leb128!(self, v, i64, write_i64_leb128)
    }

    #[inline]
    fn emit_i32(&mut self, v: i32) {
        write_leb128!(self, v, i32, write_i32_leb128)
    }

    #[inline]
    fn emit_i16(&mut self, v: i16) {
        self.data.extend_from_slice(&v.to_le_bytes());
    }

    #[inline]
    fn emit_raw_bytes(&mut self, s: &[u8]) {
        self.data.extend_from_slice(s);
    }
}

pub struct EncodeContext<'tcx> {
    encoder: MemEncoder,
    tcx: TyCtxt<'tcx>,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    interpret_allocs: FxIndexSet<AllocId>,
    relative_file: Lrc<SourceFile>,
}

impl<'tcx> EncodeContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, span: Span) -> Self {
        Self {
            encoder: MemEncoder::new(),
            tcx,
            type_shorthands: Default::default(),
            predicate_shorthands: Default::default(),
            interpret_allocs: Default::default(),
            relative_file: tcx.sess.source_map().lookup_byte_offset(span.lo()).sf,
        }
    }

    pub fn finish(mut self) -> Vec<u8> {
        let tcx = self.tcx;
        let mut interpret_alloc_index = Vec::new();
        let mut n = 0;
        loop {
            let new_n = self.interpret_allocs.len();
            // if we have found new ids, serialize those, too
            if n == new_n {
                // otherwise, abort
                break;
            }
            for idx in n..new_n {
                let id = self.interpret_allocs[idx];
                let pos = self.position() as u32;
                interpret_alloc_index.push(pos);
                interpret::specialized_encode_alloc_id(&mut self, tcx, id);
            }
            n = new_n;
        }

        let vec_position = self.position();
        interpret_alloc_index.encode(&mut self);
        self.encoder
            .emit_raw_bytes(&(vec_position as u64).to_le_bytes());
        self.encoder.finish()
    }
}

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.encoder.$name(value)
        })*
    }
}

impl<'a, 'tcx> Encoder for EncodeContext<'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);
        emit_i8(i8);

        emit_bool(bool);
        emit_char(char);
        emit_str(&str);
        emit_raw_bytes(&[u8]);
    }
}

impl<'tcx> TyEncoder for EncodeContext<'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

    type I = TyCtxt<'tcx>;

    fn position(&self) -> usize {
        self.encoder.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &rustc_middle::mir::interpret::AllocId) {
        let (index, _) = self.interpret_allocs.insert_full(*alloc_id);
        index.encode(self);
    }
}

const TAG_FULL_SPAN: u8 = 0;
const TAG_PARTIAL_SPAN: u8 = 1;
const TAG_RELATIVE_SPAN: u8 = 2;

impl<'tcx> SpanEncoder for EncodeContext<'tcx> {
    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        let id = self.tcx.stable_crate_id(crate_num);
        id.encode(self);
    }

    fn encode_def_index(&mut self, def_index: DefIndex) {
        self.emit_u32(def_index.as_u32());
    }

    fn encode_span(&mut self, span: Span) {
        // TODO: We probably should encode the hygiene context here as well, but
        // the span currently is only for error reporting, so it's not a big deal
        // to not have these.
        let span = span.data();

        if span.is_dummy() {
            return TAG_PARTIAL_SPAN.encode(self);
        }

        let pos = self.tcx.sess.source_map().lookup_byte_offset(span.lo);
        if !pos.sf.contains(span.hi) {
            return TAG_PARTIAL_SPAN.encode(self);
        }

        if Lrc::ptr_eq(&pos.sf, &self.relative_file) {
            TAG_RELATIVE_SPAN.encode(self);
            (span.lo - self.relative_file.start_pos).encode(self);
            (span.hi - self.relative_file.start_pos).encode(self);
            return;
        }

        TAG_FULL_SPAN.encode(self);
        pos.sf.stable_id.encode(self);
        pos.pos.encode(self);
        (span.hi - pos.sf.start_pos).encode(self);
    }

    fn encode_symbol(&mut self, symbol: Symbol) {
        self.emit_str(symbol.as_str())
    }

    fn encode_expn_id(&mut self, _expn_id: rustc_span::ExpnId) {
        unreachable!();
    }

    fn encode_syntax_context(&mut self, _syntax_context: SyntaxContext) {
        unreachable!();
    }

    fn encode_def_id(&mut self, def_id: DefId) {
        def_id.krate.encode(self);
        def_id.index.encode(self);
    }
}

pub struct DecodeContext<'a, 'tcx> {
    decoder: MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    type_shorthands: FxHashMap<usize, Ty<'tcx>>,
    alloc_decoding_state: Lrc<AllocDecodingState>,
    replacement_span: Span,
    relative_file: Lrc<SourceFile>,
}

impl<'a, 'tcx> DecodeContext<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, bytes: &'a [u8], span: Span) -> Self {
        let vec_position =
            u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().unwrap()) as usize;
        let mut decoder = MemDecoder::new(bytes, vec_position);
        let interpret_alloc_index = Vec::<u64>::decode(&mut decoder);
        let alloc_decoding_state =
            Lrc::new(interpret::AllocDecodingState::new(interpret_alloc_index));

        Self {
            decoder: MemDecoder::new(bytes, 0),
            tcx,
            type_shorthands: Default::default(),
            alloc_decoding_state,
            replacement_span: span,
            relative_file: tcx.sess.source_map().lookup_byte_offset(span.lo()).sf,
        }
    }
}

macro_rules! decoder_methods {
    ($($name:ident -> $ty:ty;)*) => {
        $(fn $name(&mut self) -> $ty {
            self.decoder.$name()
        })*
    }
}

impl<'a, 'tcx> Decoder for DecodeContext<'a, 'tcx> {
    decoder_methods! {
        read_usize -> usize;
        read_u128 -> u128;
        read_u64 -> u64;
        read_u32 -> u32;
        read_u16 -> u16;
        read_u8 -> u8;

        read_isize -> isize;
        read_i128 -> i128;
        read_i64 -> i64;
        read_i32 -> i32;
        read_i16 -> i16;
        read_i8 -> i8;

        read_bool -> bool;
        read_char -> char;
        read_str -> &str;
    }

    fn read_raw_bytes(&mut self, len: usize) -> &[u8] {
        self.decoder.read_raw_bytes(len)
    }

    fn peek_byte(&self) -> u8 {
        self.decoder.peek_byte()
    }

    fn position(&self) -> usize {
        self.decoder.position()
    }
}

impl<'a, 'tcx> TyDecoder for DecodeContext<'a, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

    type I = TyCtxt<'tcx>;

    #[inline]
    fn interner(&self) -> Self::I {
        self.tcx
    }

    fn cached_ty_for_shorthand<F>(&mut self, shorthand: usize, or_insert_with: F) -> Ty<'tcx>
    where
        F: FnOnce(&mut Self) -> Ty<'tcx>,
    {
        if let Some(&ty) = self.type_shorthands.get(&shorthand) {
            return ty;
        }

        let ty = or_insert_with(self);
        self.type_shorthands.insert(shorthand, ty);
        ty
    }

    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_opaque = MemDecoder::new(self.decoder.data(), pos);
        let old_opaque = std::mem::replace(&mut self.decoder, new_opaque);
        let r = f(self);
        self.decoder = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        let state = self.alloc_decoding_state.clone();
        state.new_decoding_session().decode_alloc_id(self)
    }
}

impl<'a, 'tcx> SpanDecoder for DecodeContext<'a, 'tcx> {
    fn decode_crate_num(&mut self) -> CrateNum {
        let id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(id)
    }

    fn decode_def_index(&mut self) -> DefIndex {
        DefIndex::from_u32(self.read_u32())
    }

    fn decode_span(&mut self) -> Span {
        let tag = u8::decode(self);

        match tag {
            TAG_FULL_SPAN => {
                let stable_source_file_id = StableSourceFileId::decode(self);
                let lo = BytePos::decode(self);
                let hi = BytePos::decode(self);
                match self
                    .tcx
                    .sess
                    .source_map()
                    .source_file_by_stable_id(stable_source_file_id)
                {
                    Some(v) => Span::new(
                        lo + v.start_pos,
                        hi + v.start_pos,
                        SyntaxContext::root(),
                        None,
                    ),
                    None => {
                        info!("cannot load source file {:?}", stable_source_file_id);
                        self.replacement_span
                    }
                }
            }
            TAG_RELATIVE_SPAN => {
                let lo = BytePos::decode(self);
                let hi = BytePos::decode(self);
                Span::new(
                    lo + self.relative_file.start_pos,
                    hi + self.relative_file.start_pos,
                    SyntaxContext::root(),
                    None,
                )
            }
            TAG_PARTIAL_SPAN => DUMMY_SP,
            _ => unreachable!(),
        }
    }

    fn decode_symbol(&mut self) -> Symbol {
        Symbol::intern(self.read_str())
    }

    fn decode_expn_id(&mut self) -> rustc_span::ExpnId {
        unreachable!();
    }

    fn decode_syntax_context(&mut self) -> SyntaxContext {
        unreachable!();
    }

    fn decode_def_id(&mut self) -> DefId {
        DefId {
            krate: Decodable::decode(self),
            index: Decodable::decode(self),
        }
    }

    fn decode_attr_id(&mut self) -> rustc_span::AttrId {
        unreachable!();
    }
}
