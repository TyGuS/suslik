<template>
    <div class="ide-pane editor-pane" :class="{hidden: !show}">
        <div class="editor-container" ref="editorContainer" v-once>
        </div>
    </div>
</template>

<script>
import {EditorState, EditorView, basicSetup} from "@codemirror/basic-setup"
import {Text} from "@codemirror/text";


export default {
    data: () => ({docs: {}, show: true}),
    mounted() {
        this.createEditor(this.$el);
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
        makeEditorState(text) {
            var doc = text && Text.of(text.split('\n'));
            return EditorState.create({doc, extensions: [basicSetup]})
        }
    }
}
</script>

<style>

</style>