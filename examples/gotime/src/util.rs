use std::fmt::{Debug, Display, Formatter, Write};

pub struct TextBox<T, C> {
    pub title: T,
    pub content: C,
}

impl<T, C> TextBox<T, C> {
    pub fn new(title: T, content: C) -> Self {
        Self { title, content }
    }
}

impl<T, C> Display for TextBox<T, C>
where
    T: Display,
    C: Display,
{
    fn fmt(&self, mut f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut title_metrics = MetricsWriter::default();
        let _ = write!(title_metrics, "{}", self.title);

        let mut content_metrics = MetricsWriter::default();
        let _ = write!(content_metrics, "{}", self.content);

        let gutter = 1 + if content_metrics.lines != 0 {
            content_metrics.lines.ilog10() as usize
        } else {
            0
        };

        let title_width = title_metrics.max_width;
        let min_butt_width = 3;
        let line_width = usize::max(
            gutter + 1 + content_metrics.max_width,
            2 * (min_butt_width + 1) + title_width,
        );
        let butt_width = line_width - title_width - 2;
        let left_butt = butt_width / 2;
        let right_butt = butt_width - left_butt;

        for chunk in repeated::<b'='>(left_butt) {
            f.write_str(chunk)?;
        }
        write!(f, " {} ", self.title)?;
        for chunk in repeated::<b'='>(right_butt) {
            f.write_str(chunk)?;
        }
        writeln!(f)?;

        let mut writer = LineWriter::new(f, gutter);
        write!(writer, "{}", self.content)?;
        f = writer.inner;

        for chunk in repeated::<b'-'>(line_width) {
            f.write_str(chunk)?;
        }

        Ok(())
    }
}

#[derive(Default)]
struct MetricsWriter {
    /// Current width.
    width: usize,
    /// Maximum width seen.
    max_width: usize,
    /// Number of lines
    lines: usize,
}

impl Write for MetricsWriter {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        let buf = text.as_bytes();
        let mut offset = 0;
        while let Some(newline) = buf[offset..].iter().position(|b| *b == b'\n') {
            self.lines += 1;
            self.width += newline;
            self.max_width = self.max_width.max(self.width);
            self.width = 0;
            offset += newline + 1;
        }
        self.width += buf.len() - offset;
        self.max_width = self.max_width.max(self.width);
        Ok(())
    }
}

struct LineWriter<W> {
    /// Current line number
    line: usize,
    gutter_width: usize,
    on_new_line: bool,
    inner: W,
}

impl<W> LineWriter<W> {
    fn new(writer: W, gutter_width: usize) -> Self {
        Self {
            line: 1,
            gutter_width,
            on_new_line: true,
            inner: writer,
        }
    }
}

impl<W> Write for LineWriter<W>
where
    W: Write,
{
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        let buf = text.as_bytes();
        let mut offset = 0;

        while offset < buf.len() {
            if self.on_new_line {
                write!(
                    self.inner,
                    "{:width$} ",
                    self.line,
                    width = self.gutter_width
                )?;
                self.on_new_line = false;
            }

            if let Some(newline) = buf[offset..].iter().position(|b| *b == b'\n') {
                self.inner.write_str(&text[offset..offset + newline + 1])?;
                offset += newline + 1;
                self.on_new_line = true;
                self.line += 1;
            } else {
                self.inner.write_str(&text[offset..])?;
                offset = buf.len();
            }
        }

        Ok(())
    }
}

fn repeated<const CHAR: u8>(mut times: usize) -> impl Iterator<Item = &'static str> {
    assert!(CHAR.is_ascii(), "can only repeat ASCII characters");
    std::iter::from_fn(move || {
        if times == 0 {
            return None;
        }

        let array: &'static [u8] = &[CHAR; 256];
        let chunk = &array[..times.min(array.len())];
        times -= chunk.len();
        Some(unsafe { std::str::from_utf8_unchecked(chunk) })
    })
}

pub fn display_fn<F>(f: F) -> DisplayFn<F>
where
    F: Fn(&mut Formatter<'_>) -> std::fmt::Result,
{
    DisplayFn(f)
}

pub struct DisplayFn<F>(F);

impl<F> Display for DisplayFn<F>
where
    F: Fn(&mut Formatter<'_>) -> std::fmt::Result,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        (self.0)(f)
    }
}

impl<F> Debug for DisplayFn<F>
where
    F: Fn(&mut Formatter<'_>) -> std::fmt::Result,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        (self.0)(f)
    }
}
