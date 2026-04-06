use proc_macro::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, parse_macro_input};

#[proc_macro_derive(FromU8)]
pub fn derive_from_u8(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let variants = match &input.data {
        Data::Enum(data) => &data.variants,
        _ => panic!("FromU8 can only be derived for enums"),
    };

    for v in variants {
        if !matches!(v.fields, Fields::Unit) {
            panic!("FromU8 requires all variants to be unit variants");
        }
    }

    let arms = variants.iter().map(|v| {
        let ident = &v.ident;
        quote! {
            b if b == #name::#ident as u8 => Ok(#name::#ident),
        }
    });

    let expanded = quote! {
        impl #name {
            pub fn from_u8(byte: u8) -> Result<Self> {
                match byte {
                    #(#arms)*
                    _ => bail!(CodeError::UnknownOpCodeByte { byte }),
                }
            }
        }
    };

    TokenStream::from(expanded)
}
