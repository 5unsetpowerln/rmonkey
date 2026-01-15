#[macro_export]
macro_rules! enum_with_static_str {
    (
        $(#[$enum_meta:meta])*
        $vis:vis enum $Name:ident {
            $(
                $(#[$var_meta:meta])*
                $Var:ident => $s:literal
            ),* $(,)?
        }
    ) => {
        $(#[$enum_meta])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        $vis enum $Name {
            $(
                $(#[$var_meta])*
                $Var
            ),*
        }

        impl $Name {
            /// 列挙子に紐づく &'static str（コンパイル時に固定）
            pub const fn as_str(self) -> &'static str {
                match self {
                    $(Self::$Var => $s),*
                }
            }

            /// すべての列挙子（必要なら）
            pub const fn variants() -> &'static [Self] {
                &[$(Self::$Var),*]
            }

            /// すべての文字列（必要なら）
            pub const fn strings() -> &'static [&'static str] {
                &[$($s),*]
            }
        }

        // impl ::core::fmt::Display for $Name {
        //     fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        //         f.write_str(self.as_str())
        //     }
        // }

        /// 逆変換も欲しい場合（文字列リテラルに限定しているのでパターンマッチ可能）
        impl ::core::convert::TryFrom<&str> for $Name {
            type Error = ();
            fn try_from(v: &str) -> Result<Self, Self::Error> {
                match v {
                    $($s => Ok(Self::$Var),)*
                    _ => Err(()),
                }
            }
        }
    };
}
