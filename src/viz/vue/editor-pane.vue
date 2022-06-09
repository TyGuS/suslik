<template>
    <div class="ide-pane editor-pane" :class="{hidden: !show}">
        <div class="editor-container" ref="editorContainer" v-once>
        </div>
    </div>
</template>

<style>
.editor-pane .editor-container,
.editor-pane .editor-container .cm-editor {
    height: 100%;
}
</style>

<script>
import {EditorState, EditorView, basicSetup} from "@codemirror/basic-setup"
import {Text} from "@codemirror/text";
import {suslikLanguage} from '../ts/editor';


export default {
    data: () => ({docs: {}, show: true}),
    mounted() {
        this.createEditor(this.$refs.editorContainer);
    },
    methods: {
        createEditor(parent) {
            this.cm = new EditorView({
                state: this.makeEditorState(),
                parent
            })            
        },
        open(text) {
            this.cm.setState(this.makeEditorState(text));
        },
        current() {
            return this.cm?.state.doc.toString();
        },
        makeEditorState(text) {
            var doc = text && Text.of(text.split('\n'));
            return EditorState.create({doc, extensions: [
                basicSetup, suslikLanguage, this.makeUpdateListener()]})
        },
        makeUpdateListener() {
            return EditorView.updateListener.of(v => {
                if (v.docChanged) this.$emit('change');
            });
        }
    }
}
</script>

<style>

</style>