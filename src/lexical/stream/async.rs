use crate::lexical::{Content, Error};
use std::{
    pin::Pin,
    task::{Context, Poll},
};

pub trait AsyncAnalyzer {
    type Content: Content;
    type Error: Error;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Token>>;

    fn value(&self) -> Option<Result<Self::Content, Self::Error>>;

    fn pos(&self) -> Pos;
}
